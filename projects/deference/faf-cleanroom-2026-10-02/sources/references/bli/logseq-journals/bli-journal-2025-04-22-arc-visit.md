---
journal: Daily
journal-date: 2025-04-22
---
- [scrubbed]
- First I described some of my recent interest areas to Eric (and somewhat to others):
	- `BLI`
		- In some sense, BLI gives us a heuristic estimator where the "arguments" are just "LI thinks this". Perhaps there is some way we can start with a BLI and break down the arguments a lot to get something resembling heuristic arguments?
			- This seems pretty far from ARC's intuitions on the subject, because LI's conclusions are all inductive: you start with a set of heuristics, and you see how well they work. ARC wants to use basically no inductive reasoning. It should all be "deductive" even if probabilistic.
	- `Problem of Old Evidence`
	- `text coherence`
- Over lunch, I had a conversation with Joe Carlsmith and others about corrigibility, where I ended up advocating for my `complete feedback` view of corrigibility.
  collapsed:: true
	- Joe was skeptical in the following way: the main point of my construction is to fit corrigibility in a consequentialist/utility-theoretic framework, but looking at what the construction would be like, it leans super heavily on this notion of [legitimacy](../../../corrigibility/workflow-2026-09-14/followup/legitimacy.md). Couldn't we just build a legitimacy-respecting system? Why worry about the consequentialism? More specifically, he suggested that you could have a system which behaved like a consequentialist in most cases but which behaves corrigibly when there are legitimate modification attempts. I worried that this sort of piecemeal approach would end up manipulating the humans, or other such failure modes, when acting as a consequentialist.
- Eric described some `heuristic estimators` stuff to me:
	- Heuristic estimation and detection of AI deception:
		- The idea being that if you fool multiple cameras (in the diamond example), it should be the case that the heuristic argument breaks into parts such that if you exclude some parts, it "looks very suspicious".
		- This is one reason why heuristic arguments are not supposed to be inductive at all. The heuristic estimator should not buy an argument like "if the AI fooled most of the cameras, it probably fooled all of them" -- otherwise the relationship to solving ELK breaks down.
	- What `heuristic arguments` are:
		- Heuristic arguments include logical proof steps.
		- Heuristic arguments can introduce new probabilistic models if one can prove that these probabilistic models describe frequencies in the limit; for example, it's acceptable to treat numbers as having a 50% probability of being even. This is possibly the only way you're allowed to introduce probabilities.
		- Heuristic arguments never do raw induction, where you expect something to work because it has worked many times before. They only do induction if the induction can be justified as plausible in the particular case by further heuristic arguments; you have to identify a reference class such that you can argue the behavior is appropriately uniform, justifying the induction.
		- Heuristic arguments are allowed to make independence assumptions. This is thought of as part of a broader "projection" operation which is allowed.
			- EG, independence can be thought of as taking a probability distribution that's too difficult and approximating it with the closest fully factored distribution.
			- We can also think about more complex approximations, something like variational methods. A complex thing can be approximated as a sum of terms or a product of factors, etc.
		-
	- Generalizing independence assumptions for heuristic estimators:
- [scrubbed]
-