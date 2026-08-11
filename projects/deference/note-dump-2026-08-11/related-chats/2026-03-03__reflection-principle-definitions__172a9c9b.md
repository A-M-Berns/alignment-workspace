---
title: "Reflection principle definitions"
uuid: 172a9c9b-b292-47bf-9da2-3f6fcc50cf93
date: 2026-03-03
source: claude.ai
messages: 4
keywords: ["logic", "philosophy", "epistemology", "probability", "mathematics"]
---

# Reflection principle definitions

**Summary.** Explanation of reflection principle across multiple mathematical contexts: van Fraassen's probabilistic version (credences should defer to expected future credences), set-theoretic version (properties of universe reflect to smaller sets), and Schwarz reflection principle in complex analysis. User interested in van Fraassen version; discussion covers diachronic coherence and implications for rational agents.

**Where to look:**
- 1-2: Overview of reflection principle in three contexts
- 3-4: Details of van Fraassen probabilistic reflection principle and diachronic Dutch book

---

## [1] Human — 2026-03-03T18:54:33.478644Z


Definition of the reflection principle

## [2] Claude — 2026-03-03T18:54:52.090225Z


<details><summary>thinking</summary>

The user is asking about the definition of the reflection principle. This could refer to several things depending on context:

1. The reflection principle in probability/Bayesian reasoning (which is referenced in their user preferences)
2. The reflection principle in set theory (large cardinal axioms)
3. The reflection principle in complex analysis (Schwarz reflection principle)

Given the user's background in AI safety, Agent Foundations, and the fact that their user preferences explicitly mention a reflection principle in the context of beliefs, they most likely mean the probabilistic reflection principle (van Fraassen's reflection principle or similar). But they might also be interested in the set-theoretic one, or they might want a general overview.


Let me lay out the main versions. The probabilistic reflection principle says that your current beliefs should defer to your expected future beliefs—if you think you'll assign probability c to some event, you should assign it probability c now. The set-theoretic version is about large cardinals: any property that holds of the entire universe of sets should also hold of some smaller set or level. There's also the Schwarz reflection principle in complex analysis, though that's less likely what they're asking about.

Given their preferences lean toward the probabilistic interpretation, I'll focus there but acknowledge the other contexts exist. This is straightforward enough that I don't need to look anything up.

</details>

Which one? The term appears in several fields:

**Probabilistic (van Fraassen):** If $P$ is your current credence function and $P'$ is your credence function at some future time (after legitimate updating), then $P(A \mid P'(A) = c) = c$. Your current credences should already agree with whatever you expect your future credences to be. Violations imply you currently have information you're not acting on.

**Set-theoretic:** Any first-order property that holds of the universe $V$ already holds of some $V_\alpha$. So the universe can't be uniquely characterized by any single first-order sentence — any such property "reflects down" to a rank. This is used to motivate large cardinal axioms, since you can argue that certain second-order or schematic properties should also reflect.

**Complex analysis (Schwarz):** An analytic function defined on one side of a boundary can be extended to the other side under appropriate conditions.

You reference the probabilistic version in your preferences. Were you looking for a precise statement of that one, or one of the others, or something else entirely?

## [3] Human — 2026-03-03T18:55:39.781912Z


Yeah you're good the van f one

## [4] Claude — 2026-03-03T18:55:50.106864Z


<details><summary>thinking</summary>

The user wants more detail on van Fraassen's reflection principle. Let me give a precise statement and some context.

</details>

The standard formulation: if $P_t$ is your credence function at time $t$ and $P_{t'}$ is your credence function at a later time $t' > t$, then for any proposition $A$:

$$P_t(A \mid P_{t'}(A) = c) = c$$

That is, if you currently expect that your future self will assign credence $c$ to $A$, you should already assign credence $c$ to $A$ now.

The intuition is that your future credences constitute evidence. If you know you'll believe something later (after legitimate updating), and you don't believe it now, you're leaving money on the table — you have information (namely, the prediction about your future state) that you're not incorporating.

Van Fraassen introduced it in "Belief and the Will" (1984). He argued it's a diachronic coherence constraint analogous to synchronic Dutch book arguments: an agent violating reflection is vulnerable to a diachronic Dutch book.

There are well-known caveats. The principle assumes the agent expects their future updating to be legitimate — no memory loss, no brainwashing, no foreseeable irrationality. If you expect to get drunk tonight, you should *not* defer to your future drunk credences. This is essentially the distinction you're drawing in your preferences between legitimate and illegitimate thinking.

Anything specific you wanted to pin down, or was this just a definitional check?
