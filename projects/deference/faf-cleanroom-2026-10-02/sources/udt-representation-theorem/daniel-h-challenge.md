# The Daniel Hermann Challenge

## The Core Question

**Daniel H's framing:** The fundamental question for UDT is "how do you group decision problems?"

- Default answer: Take them one at a time → updateful reasoning (EDT)
- UDT answer: Group them into policies → updateless reasoning

Daniel is happy to say that if you're asking "what's the optimal policy?", UDT is the right answer. But if you're asking "what's the optimal decision?", EDT is the right answer.

**His challenge:** What justifies grouping decision points together? Why should the notion of a "decision problem" include the whole policy rather than a single decision?

## Why This Is Hard

The UDT advocate has been "decorating" the action variable with a function from observations. This is adding structure. Why is this extra structure justified?

From Daniel's perspective:
- EDT comes naturally from representation theorem type work (Jeffrey-Bolker)
- UDT requires additional justification for the policy structure
- He hasn't seen a write-up that meets his standards

## Transparent Newcomb: A Key Test Case

**Setup:** You face an empty big box and a small box with $1K. You can take just the big box (one-box) or both (two-box).

**EDT reasoning:** The big box is empty. Taking both gets $1K. Taking just the big box gets $0. Two-box.

**UDT reasoning:** If I were a one-boxer, Omega would have filled the big box. By being a two-boxer, I ended up in this bad situation. I should have been a one-boxer.

**The parallel to original Newcomb:**
- In original Newcomb, CDT says "I wish I could be a 1-boxer but I'm just not that type"
- In transparent Newcomb, EDT says "I wish I could be a 1-boxer but see, the empty box proves I'm not"

Both are accepting a bad outcome because they think they can't change their type.

**UDT response:** You CAN change your type by choosing differently. The type just IS the policy you implement.

## Daniel's Likely Response

**"But this involves two decision points"** - when you see the big box empty, and when you see it full. The UDT analysis groups them together.

**Counter:** Something about analyzing the empty-box case in isolation is absurd. The problem description *implies* the relevance of the full-box case. The two cases are defined by their relationship to each other.

This is where we need the justification for grouping.

## "Why Ain't'cha Rich" Arguments

**The argument:** EDT makes more money in Newcomb. CDT makes more in other cases. UDT claims to get rich in the most scenarios.

**Counter 1 (Whose criterion?):** Different DTs have different optimality criteria. "Why ain't'cha rich" just applies one DT's criterion to another. CDT doesn't think the money was available. EDT doesn't think the money in transparent Newcomb was available.

**Counter 2 (Punishing rationality):** Decision problems can be designed to punish any decision procedure. So not-being-rich isn't automatic proof of irrationality.

**UDT Response to Counters:**

The "why ain't'cha rich" arguments connect with reality better than the counters suggest. The counters are sophisticatedly defending suboptimal policies.

The "punishing rationality" counter is addressed by Yudkowsky's fairness: a problem is fair if it depends only on what an agent *does*. If you're only checking actions (including policies), you can't punish rationality.

**Key insight:** We want the broadest possible notion of fairness that still admits a good decision theory. If a narrower theory (UDT) gets more problems right while still getting the easier problems right, it's the better theory.

## "Decision Theory is for Making Bad Outcomes Inconsistent"

(From Nate Soares)

**The idea:** Decision theory should rule out bad outcomes by making them inconsistent with the agent's existence/behavior.

**Application to transparent Newcomb:** UDT agents won't see the empty box (or will see it with low probability). So "what would UDT do facing the empty box?" is the wrong question - it's an inconsistent scenario for a UDT agent.

**Application to Smoking Lesion:** EDT agents can't statistically match the population in Smoking Lesion (if they're making decisions the EDT way). So the problem is "wrong" - it describes an inconsistent situation.

**The quantitative version:** Even if we're not rejecting situations outright, we should judge decision theories by the *method of putting agents into situations*, not just by offering a scenario. The empty-box case comes paired with the full-box case.

## The "Space Cadets" Objection

**Academic DT position:** Decision theory should give normative advice even to people who won't take it (non-normative agents, "space cadets").

**This favors:** The "each decision is separate" framing. You're advising on THIS decision, not on the whole policy.

**Counter:** If decision theory is about advice, then doing something due to advice should be the same as doing it for your own reasons. This is a fairness condition.

The CDT analysis of Newcomb imagines that if you give advice, Omega can't predict anymore. But Omega CAN predict advice-following! This is part of the problem description.

## Connection to Agency

Sam's point: Daniel's framework treats the epistemic state as prior to agency. "God gives you an epistemic state, then you analyze."

But this is wrong:
1. An epistemic state underspecifies a decision problem (need counterfactual structure)
2. Agency involves reflective awareness of one's own agency
3. Decision moments are parts of agents, not independent points

**Heidegger connection:** "A moment can't be seen in isolation." Decision points are defined by their relationships to other decision points - past, present, future. This is the structure that UDT respects.

## The Justification We Need

To satisfy Daniel H, we need:

1. **A story about what decision theory is for** - not just giving advice to space cadets, but characterizing good reasoning for agents in the world

2. **An argument that agents naturally span multiple decision points** - you can't recognize a decision moment without first recognizing it as part of an agent

3. **A representation theorem** - axioms on agent reasoning → UDT

The key is (2): why do decision points belong together in policies?

**Arguments for (2):**

- **Functional identity:** Same algorithm applied at different inputs
- **Unity of agency:** Modeling X as a single agent means modeling a single optimization
- **Temporal structure:** Moments are defined by relationships to other moments
- **Fairness:** The broadest notion of fairness that admits a good DT is the one that checks policies

## The Representation Theorem Structure (Daniel-Satisfying Version)

**Setup:** You're modeling something as an agent.

**Axiom 1 (Unity):** You're modeling a SINGLE agent, not a collection of independent decision-makers.

**Axiom 2 (Spanning):** This agent faces multiple situations (observations).

**Axiom 3 (Coherence):** The agent's behavior across situations is coherent (same utility, same reasoning).

**Axiom 4 (Fairness):** The environment responds to behavior, not to mechanism.

**Theorem:** Such an agent reasons updatelessly.

**Why this should satisfy Daniel:**

The axioms are about what it means to model something as a "single agent." They're not assuming UDT; they're characterizing agency.

The theorem says: if you accept these axioms (and Daniel should, if he accepts modeling things as single agents), then UDT follows.

The alternative (EDT on individual decisions) fails the Unity axiom - it treats decision points as separate optimizers.

## Key Quote to Remember

> "My instinct is that cutting it up is the thing that needs to be justified. If you cut it up and you find that you leave utility on the table because you cut it up... [that's a problem]."

The burden of proof is on the cutter-upper, not on the policy-thinker.
