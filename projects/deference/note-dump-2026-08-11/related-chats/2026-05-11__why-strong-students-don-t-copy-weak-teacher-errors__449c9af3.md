---
title: "Why strong students don't copy weak teacher errors"
uuid: 449c9af3-e65f-4ca9-b5af-f7130f967732
date: 2026-05-11
source: claude.ai
messages: 4
keywords: ["weak-to-strong generalization", "pretraining", "inductive biases", "elicitation", "optimization", "machine learning", "noisy labels", "reward modeling", "alignment", "superhuman capabilities"]
---

# Why strong students don't copy weak teacher errors

**Summary.** Technical discussion of the theoretical puzzle in weak-to-strong generalization: why strong models trained on weak teacher labels don't learn to copy the weak teacher's errors despite proper scoring rules suggesting they should. Claude provides a detailed answer centered on how pretraining encodes human concepts, making the 'laziness' of limited optimization naturally preserve correct concepts while skipping teacher-specific errors. The conversation culminates in a critique of W2SG's applicability to superhuman capabilities where no pretrained representation exists to elicit.

**Where to look:**
- 1-2: Problem statement and literature review with extended search results on W2SG mechanisms
- 3: Clarification question about why laziness points toward correct concepts rather than incorrect ones
- 4: Main answer covering pretraining alignment, hypothesis space structure, and critique for superhuman regime; Frame Break section on fundamental limits of elicitation mechanism

---

## [1] Human — 2026-05-11T14:23:27.582312Z


In weak-to-strong generalization, why doesn't the strong student learn to copy the weak teacher's errors, at least approximately? It is like a student learning from a textbook full of typos. A human student will try to get past the typos because they have some concept of a real intended text behind the typos; they know the typos don't carry useful information which will generalize. ML models have no such concept; they're just trying to predict well. The usual story behind weak-to-strong generalization (as I understand it) is that the strong student nonetheless isn't SO strong that it can actually predict the typos; typos are really hard to predict, so the intended text mostly shines through. However, this story does not sit right with me: it seems like the strong student should nonetheless introduce typos at the observed frequency, even if the specific typos cannot be predicted exactly; otherwise, they'll suffer predictive loss. This argument seems general: if the errors of the teacher can't be precisely predicted, and you're learning via a proper scoring rule, then you'd better at least treat those errors as stochastic! This seems to imply that weak-to-strong won't happen: the strong student should have a similar error rate to the weak teacher.

## [2] Claude — 2026-05-11T14:25:57.194652Z


<details><summary>thinking</summary>

 The user is raising a genuinely compelling technical point about weak-to-strong generalization—if a strong model trains on weak teacher labels using proper scoring rules, shouldn't it at least match the teacher's error rate rather than exceed it? This seems like it deserves careful thought rather than a quick response.

The core tension is that under infinite data and a proper scoring rule, the Bayes-optimal predictor should recover the exact error distribution of the weak teacher. Yet the empirical results from weak-to-strong generalization papers show strong models sometimes outperforming their weak teachers. The likely explanations involve finite data regimes, the strong model's pretrained inductive biases pulling it toward correct answers, the optimization process not actually reaching the Bayes-optimal solution, early stopping effects, or architectural constraints that prevent perfect overfitting to the weak labels. t - and this is precisely why w2s only partially closes the gap, not fully

Actually, I think the user's argument is largely correct and well-known in the literature. The standard answer involves:

1. The strong model has limited capacity (in some sense) to fit the noise - it's biased toward "natural" solutions that exist in its pretrained representations
2. With finite data, regularization/early stopping prevents fitting the noise
3. The pretrained model has prior beliefs that pull it toward correct answers
4. There's an "elicitation" framing - the strong model already knows the answer, the weak labels just elicit it

The user's argument essentially is: in the limit of infinite data and capacity, w2s should fail. This is correct! W2s works because of finite data and inductive biases. The original Burns et al. paper discusses this.

There's also the question of what "errors" means - if the weak teacher's errors are systematic (predictable patterns of mistakes), then yes, the strong student would learn those patterns. If they're random noise, then under a proper scoring rule with infinite data, the student would predict the noisy distribution. But with limited data, fitting noise is hard.

The key insight is that even a sufficiently powerful student could theoretically overfit to the teacher's errors, but regularization and pretraining inductive biases work against this. The correct answer is more "salient" in the pretrained representations than the teacher's idiosyncratic mistakes, so it requires less complexity for the strong model to learn - it's essentially an Occam's razor argument where the right answer has a simpler representation than the noisy version.

The weak teacher's labels aren't pure noise though - they're correlated with ground truth, and the strong student can latch onto that signal because it's both predictively useful and natural given its pretraining. I think this is a substantive question I can engage with directly, and I should probably ask what specific aspect the user wants to explore rather than just launching into research mode. The user has research mode enabled and this is a complex technical question, so I should launch the extended search tool—that aligns with both the system instructions and what the user is asking for. my analysis alongside the research findings.

I'm weighing whether this theoretical question really needs a web search or if it's better handled as a direct conceptual discussion. The user's argument is precise and mathematical, so research could surface the weak-to-strong generalization literature and related work, but I should focus the search narrowly on why the proper-scoring-rule mechanism doesn't force the student to match the teacher's error rate.

Let me run a targeted search to find what the original paper and follow-ups actually say about this specific puzzle.

</details>

Your question is clear and specific - it's a genuine theoretical puzzle about weak-to-strong generalization (W2SG) that deserves careful investigation. Let me dig into the literature on this. I'll look for both the original Burns et al. (2023) paper's framing and follow-up theoretical/empirical work that directly addresses the proper-scoring-rule argument you've raised.

*[tool call: launch_extended_search_task]*

*[tool result: launch_extended_search_task]*

Your investigation into the proper-scoring-rule objection to weak-to-strong generalization (W2SG) is ready. The report confirms that your argument is correct asymptotically and is explicitly conceded by Burns et al. (2023), then maps the four main mechanisms the literature uses to explain why W2SG nonetheless works in practice: restricted hypothesis classes (Lang–Sontag–Vijayaraghavan; Charikar–Pabbaraju–Shiragur), benign overfitting in overparameterized regimes (Wu & Sahai), elicitation of pretrained priors (Somerstep et al.), and finite-epoch optimization. It covers empirical failure modes (reward modeling PGR ~10%, EleutherAI's null replication results, Yang et al.'s deception findings), the connection to classical noisy-label learning, Demski's Bayesian critique, and an assessment of where the live open questions remain.

*[tool call: artifacts]*

*[tool result: artifacts]*

## [3] Human — 2026-05-11T14:57:16.289957Z


If the phenomenon is due to the inductive biases of weak optimization, why does it work? It seems to depend on a coincidence between those inductive biases and human ideas. EG, the student would optimally mimic the typos in the textbook, at least by introducing typos at the same frequency, but the student is 'too lazy' to do so. Why does laziness point in the direction of skipping the typos rather than skipping the valuable ideas in the textbook? I get that it's a fragile phenomenon, but under what circumstances will this happen?

## [4] Claude — 2026-05-11T14:58:22.180674Z


 

<details><summary>thinking</summary>

 The user is raising a sharp point—if weak optimization and inductive biases explain W2SG, why do those biases steer toward correct content rather than noise? It's like asking why a lazy student skips typos instead of skipping the actual material. I need to think through what's actually driving this. The key insight seems to be that pretraining did the heavy lifting here, not the finetuning process itself.

During pretraining on massive data, the strong model developed rich representations for ground-truth concepts because they're genuinely useful for prediction and appear across many contexts. The weak teacher's specific errors, by contrast, are idiosyncratic—they don't appear in any structured way in the pretraining data. So when finetuning begins with small updates, the model already has strong features for the correct concept but essentially no features for "this particular teacher's error patterns." Under SGD, it's a much shorter gradient path to move toward what's already well-represented than to build entirely new representational structure for the teacher's quirks.

The lazy training perspective reinforces this: if finetuning only makes small perturbations in feature space, the ground-truth concept—which was already salient from pretraining—remains the natural attractor, while learning the teacher's idiosyncratic errors would require building something fundamentally new.

The typo analogy sharpens this intuition. A human reader encountering a typo-ridden textbook would need to actively learn what specific typos this text contains and then apply those patterns—essentially learning a new skill that conflicts with their deeply ingrained language model. Even if the typos were systematic (always "teh" instead of "the"), the reader's lifetime of correct spelling creates a strong prior against reproducing them. Random typos are even harder to learn because there's no predictable pattern to acquire.

This is where the argument breaks down for systematic teacher errors. If the weak teacher's mistakes follow a consistent pattern—a particular logical fallacy or recurring bias—the student can and will learn to replicate it, which is exactly why Burns et al. found that weak-to-strong generalization fails so badly in reward modeling scenarios. The ground-truth concept has a simpler description (it's a natural, frequently-seen concept), while the teacher-with-errors concept requires a longer description (ground truth plus a specific error pattern). Neural networks' inductive biases favor shorter, simpler explanations, so the model naturally gravitates toward the cleaner ground truth rather than the more complex teacher-error hybrid.

But this Occam's razor argument only holds if the ground-truth concept is actually simpler than the noisy version—and that's only true because pretraining already embedded the ground truth deeply. The strong model absorbed human concepts throughout pretraining on vast text corpora, so those natural concepts are far more salient than the teacher's specific errors, which never appeared in the pretraining data. The real insight is that pretraining encoded human concepts because it trained on human-generated text, so there's a fundamental alignment between what the model's inductive biases favor and what we actually want it to learn. Weak-to-strong generalization only works because this alignment was baked in from the start through human data.

The Lang et al. expansion theory formalizes this: the strong model's hypothesis space is structured so that fitting the teacher's mistakes would require fitting a whole neighborhood of related examples, many of which the teacher gets right—making those mistakes costly. The student's smooth hypothesis class naturally resists fitting errors that violate the task's underlying geometry, and if that geometry is human-meaningful, then this laziness preserves human values.

But this breaks down in several ways: when the teacher's errors align with natural features the strong model learned from pretraining, when training runs long enough to overcome the inductive bias, when the strong model gets heavily finetuned and loses its pretrained prior, when the weak labels are structured and rich like reward models, or when the strong model can actually predict what the weak teacher will get wrong. The core insight is that "laziness" really means making minimal changes to the pretrained model, and since the pretrained model already contains the ideas but not the typos, small perturbations naturally preserve the former while skipping the latter.

Now I'm thinking about how to actually answer this for someone who knows ML deeply—they want substance, not a survey. I should give them a direct response without unnecessary scaffolding, keeping it cognitively engaging rather than just listing facts.

The core insight is that pretraining already did the alignment work, so the model's "laziness" is really just preferring its existing aligned representations over building new machinery to encode the teacher's errors. Since the ground-truth concept is already there in the pretrained weights, small gradient updates naturally express it, while adopting the teacher's mistakes would require larger updates that don't fit the optimization landscape. This works cleanly when the teacher's errors are genuinely orthogonal to the pretrained concepts, but breaks down if the errors are entangled with them or if the model needs to learn something fundamentally new. imization doesn't take in a few epochs.

This means the "coincidence" is really not a coincidence: pretraining on human text already encoded human concepts. The weak teacher's role is just to select / activate / elicit the already-encoded concept rather than to teach the strong model what the concept is.

Why doesn't laziness skip the valuable ideas? Because the valuable ideas are *not* what the optimizer needs to learn — they're already in the strong model. The optimizer only needs to learn "which existing representation to output." This is a small change. By contrast, the typos/errors require building new representational machinery from scratch — a much larger change.

In the textbook analogy: a human student reading a typo-ridden textbook DOES preserve their pre-existing spelling knowledge (the "valuable ideas") because reading doesn't teach them new spelling. They have to actively learn to imitate typos, which is harder than just reading correctly.

This approach breaks down in several scenarios: when the teacher's errors happen to be natural concepts the strong model already knows from pretraining, when training runs long enough to actually learn the noise, when the strong model's pretrained knowledge is weak, when the weak labels contain enough structure to push toward the noise, or when pretraining never encoded the relevant concept in the first place. That last case is the critical limitation for superhuman capabilities.

The real concern for alignment is that weak-to-strong generalization fundamentally works by eliciting concepts already present in the pretrained model. If we're trying to align a superhuman system on tasks where the correct answer lies beyond what's encoded in human text, then there's nothing to elicit — the right answer simply isn't in the pretrained representation. That's where the approach hits its deepest limit.

</details>

The non-coincidence is that pretraining already did the alignment work — and "laziness" means laziness *with respect to the already-aligned pretrained representation*, not laziness in some absolute sense. The textbook analogy is actually quite apt, and unpacking it carefully shows why:

A human reader of a typo-ridden textbook does preserve their pre-existing spelling competence (the "valuable ideas") while skipping the typos. Why? Because their spelling knowledge was *already established* before encountering this textbook, and reading the typos does not actively retrain it. To match the textbook's typo frequency, the reader would have to *learn a new skill* — typo-generation — which is harder than just continuing to spell correctly. The valuable ideas, by contrast, slot into pre-existing conceptual machinery; absorbing them is "the cheap thing." The asymmetry is not in the textbook, it's in the reader's prior state.

This maps onto W2SG cleanly. The strong model's pretrained representation already encodes a rich features for human-meaningful concepts because pretraining was done on human-generated text. The weak teacher's specific error pattern is *not* in pretraining — it's idiosyncratic to that particular teacher. So under finetuning with limited updates (few epochs, LoRA, small learning rate), the SGD trajectory expresses what's already there rather than building new representational machinery for the teacher's noise. The "correct" concept and "teacher's noise pattern" are not symmetric: the first is a small distance from the pretrained state; the second requires a substantial detour. Lang–Sontag–Vijayaraghavan's expansion property is a formal version of this: the student's hypothesis class is structured so that fitting the teacher's errors would *also* require sacrificing accuracy in nearby correct regions, making the noise-fitting solution locally non-optimal.

So the "coincidence" between inductive bias and human concepts is not really a coincidence at all — it is *causally inherited* from pretraining on human text. W2SG works to the extent that pretraining has already encoded the target concept; weak labels then serve to *select* the right concept from the model's hypothesis space rather than to *teach* the concept from scratch. This is what "elicitation" means rigorously: the weak teacher provides few bits of information (just enough to pick out the right concept) and these few bits hit a pre-shaped landscape.

The conditions under which it works are therefore:

- The target concept must be well-represented in the strong model's pretrained features (the harder the concept is to elicit from pretraining alone, the worse W2SG performs).
- The weak teacher's errors must *not* themselves correspond to natural concepts the strong model has learned. This is why the technique works for label-noise on standard NLP tasks but fails for reward modeling: preference errors are structured, predictable, and often correspond to features the model already represents (sycophancy, length bias, etc.), so the student can fit them with the same machinery it uses for the true preferences.
- The weak teacher's errors must be locally "expansive" — fitting them in one region must imply errors in correlated regions where the teacher is correct, so that the cross-entropy gradient pushes against the noise-fitting direction.
- Finetuning must be limited (few epochs, low capacity adapters, regularization) so that the optimizer does not have time to build new representational structure for the noise pattern. The Burns et al. U-shaped curves directly demonstrate this: keep training and the student does eventually imitate the teacher.

> **Frame Break:** Notice what this implies for the original superalignment motivation. W2SG works because pretraining encodes the target concept and weak labels just select it. For *superhuman* capabilities — the case the technique was supposed to address — there is by hypothesis no pretrained representation of the correct answer to elicit, because the correct answer was never in the human-generated training corpus. The elicitation mechanism that explains why W2SG sidesteps the proper-scoring-rule argument is exactly the mechanism that should fail to scale to the regime W2SG was proposed for. This is, I think, the deepest version of the critique you were circling, and it is sharper than "the phenomenon is fragile." The phenomenon's mechanism is *structurally bound* to the sub-human regime where pretraining already contains the answer.

The cleanest way to test whether W2SG transfers to genuinely-beyond-pretraining tasks would be to construct a target concept demonstrably absent from the pretraining corpus and see whether weak supervision can still elicit superior performance. To my knowledge, no published experiment has done this in a clean way; all current evidence comes from tasks where the strong model plausibly already knows the answer from pretraining. The Burns et al. ChatGPT reward modeling result (PGR ≈ 10%) may already be hinting at this failure mode, since human preferences encoded in pretraining are an imperfect proxy for the actual reward-modeling target.
