# Dispatch

The round was dispatched as a conversation. The maintainer's messages follow in order,
verbatim; the executor's replies between them are not reproduced.

## 1

https://www.sameisenstat.net/doc/condensation-25-07.pdf 
https://arxiv.org/pdf/2109.10996

I'd like to start thinking about "naturalized agency" as building on Cartesian Frames (and perhaps other mathematizations of agency) and Condensation towards something like a more objective and mathematical take on Dennett's Intentional Stance

Initial thoughts from a different thread: Here is a draft. It is written to stand alone, and it marks which thoughts are yours and which are mine and unverified.

---

**Starting a thread on naturalised agency**

I want to explore a direction I'm calling naturalised agency. This message gives the background and where an earlier conversation got to. I'm attaching two papers:

- Sam Eisenstat, "Condensation: a theory of concepts"
- Garrabrant, Herrmann and Lopez-Wild, "Cartesian Frames" (arXiv:2109.10996)

**What I'm after**

My overall research program is a formal theory of good behaviour, something like a physics of normativity: formal concepts of things like corrigibility and non-manipulation that admit theorems of the form "if these conditions hold, approximately, then this good behaviour follows, approximately". The formal setting should read correctly against existing philosophy, and the conditions should be defensible, feasible for real systems, and not quietly assume the problem away.

This thread is about a related but separate interest. I'm drawn to the Dennettian, intentional-stance way of doing agent foundations: start from a more undifferentiated, naturalistic picture of the world, with no agents marked in it, and model somewhat formally the idea that "here is an agent, there is an agent". I'd like to emphasise the normative side of that. I think it probably builds on Condensation together with Cartesian frames.

I think an objectivity theorem for the intentional-stance view would be powerful.

Please keep this separate from my work on manipulation and legitimacy. There are connections, noted below, but I don't want the two merged.

**Where the earlier conversation got to**

These are the assistant's thoughts from reading the Condensation paper in full and the first part of the Cartesian frames paper. Treat them as proposals to check, not results.

*What each paper supplies.* Cartesian frames give the space of ways to carve a world into an agent and an environment, and relations between carvings (coarsening, subagents). They are about what could happen, have no probabilities, and do not say which carvings pick out real agents. Condensation gives a criterion for which latent variables are real: posit a latent for each subset of the observed variables, standing for what those observables share, and score a model by how compactly it accounts for them. Its main theorems say two good models of the same observables must have corresponding latents, exactly or approximately. It is about a single distribution and has no notion of choice. So one supplies possible boundaries with no reason to prefer any, and the other supplies a reason to prefer some descriptions with no notion of an agent.

*A possible combination.* Take a candidate carving and treat the system's response in each of many situations as an observable. Ask whether those responses condense around a shared latent: one recoverable from enough of its behaviour, and given which the rest is predictable from the local situation. "This is an agent with that aim" would mean its behaviour condenses in that way. This would make Dennett's "real patterns" checkable, since the condensation score is a precise form of "pays off in prediction".

*The objectivity theorem.* The paper's approximate comparison theorem has a corollary that seems to fit: if in one observer's model the latent shared by all the behaviours is nearly recoverable from any k of them, and the other observer's model nearly satisfies the paper's independence condition, then the first observer's shared latent is nearly determined by the second's. That would answer the standard objection that attributing aims is in the eye of the beholder. It would also say how objective attribution is as a function of how revealing the behaviour is: varied behaviour forces agreement, and sparse behaviour permits a bounded amount of disagreement. That would turn the old dispute about indeterminacy of interpretation into a quantity. The bound carries a large combinatorial factor, and this reading of the corollary has not been verified.

*The normative part.* The intentional stance assumes the system does what it has reason to do given its aims and information. So a full attribution has an aim, a picture of how things are, and a rule for what such a system ought to do. What the rule does not account for is a mistake. That suggests a naturalised reading of "function" (the worldly quantity a part's state carries information about) and of "mistake" (a departure from what the attributed aim and information call for).

*Gaps already visible.*
1. Condensation has one distribution and no choice; frames have choice and no probability. Bridging them is the main technical problem.
2. Condensation starts from a given list of observables, which already carves the world.
3. The theorem gives objectivity of shared structure, which is not yet an aim. A thermostat's set point is shared structure too. The models need a rational form for the result to be about the intentional stance.
4. Belief and desire cannot be separated from behaviour alone. Objectivity is likely for the policy-relevant latent as a whole. The split probably needs direction of fit, hence time or causal order.
5. Trivial agents: the description by aims has to beat a plain mechanical description, so the criterion should compare scores.
6. One latent per subset of observables grows very fast.

*Unverified guesses.* That the lattice of latents indexed by subsets lines up with the subagent relation in frames. That the approximate corollary gives uniqueness of attributed aims in the way described.

*Suggested first step.* Work one small case by hand: a simple controller with a set point, observed across a handful of situations, with two differently built models of it. Compute the scores and see whether the correspondence holds with the stated bound.

**Connections to my other work, for awareness only**

- In the manipulation work, the open question is when an adviser is trying to bring about someone's mistake. An intentional-stance account of "trying" might eventually answer it.
- My workspace already has a Lean bridge to Cartesian frames, and some earlier results are stated in that frame's terms.

**How I'd like to work**

Be honest and direct, and be a neutral judge of each idea: press on it without leaning optimistic or pessimistic. Negative results count. Say plainly what you have verified and what you are guessing. I'd rather have a small thing that is right than a large synthesis that has not been checked.

---

Two things you may want to adjust before sending: the "what I'm after" section paraphrases you closely but is my wording, and the last section restates preferences you have given me that the new thread may already have from your standing instructions.

## 2

I think also like I guess I'm thinking of this as a new mathematical theory with these two ingredients as inspirations. But what I really want is a formal theorem of something like objectivity for the Dennettian intentional stance towards agency rather than strictly a "combination of CF and condensation" if you know what I mean

## 3

Yes I agree this has to build past this negative result https://proceedings.neurips.cc/paper_files/paper/2018/file/d89a66c7c80a29b1bdbab0f2a1a94af8-Paper.pdf
And yeah I'm not expecting like "pure objectivity". More like maybe formal tools to say in some mathematical way like if I just give you an undifferentiated picture of the world a way to say something like here are roughly the loci of agency in the world. (Something like CF also shows you that this can't be purely unique nor should it be e.g. is the agent the guy on the motorcycle or the guy and the motorcycle together?)

## 4

Is there other stuff you want to read before we begin

## 5

https://www.lesswrong.com/s/2A7rrZ4ySx6R8mfoT
https://ruccs.rutgers.edu/images/personal-zenon-pylyshyn/class-info/FP2012/FP2012_readings/Dennett_RealPatterns.pdf
https://web.stanford.edu/~paulsko/papers/DennettTB.pdf
https://www.lesswrong.com/posts/znfkdCoHMANwqc2WE/the-ground-of-optimization-1
https://arxiv.org/pdf/2402.10877

## 6

Do you want to just like chat for a moment after you ingested all of that before we start the real math

## 7

Yeah I'm not sure "steering" is necessarily the right primitive? I think something more teleological like function and purpose is definitely more close to what I want to be studying here. I do think Dennett's work is very related to this stuff

## 8

I think perhaps role and self-maintenance? Can we talk more about how to pin this down more or like more thoughts or questions that push in the direction of the kind of framework we want to develop

## 9

I would say a hurricane or flame doesn't really have a function
A thermostat's function is definitely bestowed from elsewhere
I think the trained model part is right as you phrased it mostly

## 10

yeah this is very close to what i was thinking. Do you want to look at the chemistry math you mentioned or other existing formalisms of any kind just for more inspiration?

## 11

Anything else you want to do now?

## 12

Go for it

(Attached: `artl_a_00125.pdf`, Beer, "The Cognitive Domain of a Glider in the Game of Life".)

## 13

Can you tell me more clearly where we're at and what you want from me? wrt the carving problem or any other like modeling stuff that we should try to iron out

## 14

i think probably dropping bestowed as a separate category is a good idea. In terms of the three examples, idk i think i'd say the bacterium has an aim? and the model too? and mayyybe not the thermostat? these are held pretty loosely tho

## 15

Idk I don't have strong opinions here tbh. I think I'd like some of these philosophical choices to be more like derived from the mathematical experimentation rather than just posited? Except insofar as we're following e.g. Dennett

## 16

keep going

## 17

Can you explain the math of what's going on rn

## 18

So is this roughly an objectivity theorem for intentional-stance agency like we wanted or are we not quite there yet?

## 19

Ok let's just keep that in mind as the end goal, but we can keep building up this teleological stuff which I do think is very important

## 20

Keep going

## 21

Keep going

## 22

Get a PR with this started and then keep going
