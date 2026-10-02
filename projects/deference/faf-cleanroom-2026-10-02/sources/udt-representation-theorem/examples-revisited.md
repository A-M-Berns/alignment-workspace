# Examples Revisited: From Representation Theorem to Self-Trust

> **Corrected 2026-08-05** (see [cleanup-audit-2026-08-05](cleanup-audit-2026-08-05.md)): the original version of this file claimed functional identity *resolves* Coordinated Buttons and Third Button, and diagnosed the Memory Problem as a decision-determination failure. All three claims were wrong against the source ([communication-trust-translated](communication-trust-translated.md), Motivating Examples). This version states what the examples actually show. The uncorrected original is in git history.

## Goal

Connect the representation theorem framework to the examples in [communication-trust-translated](communication-trust-translated.md):
1. Coordinated Buttons
2. Memory Problem
3. Third Button

These are the framework's concrete test cases. Honest scorecard: the framework *illuminates* all three but *resolves* none of them outright — each exposes a specific piece of machinery the representation theorem still needs.

---

## Example 1: Coordinated Buttons

### Setup
You are about to be copied. You and your copy will be in separate rooms (red/green) with buttons labeled $5 and $10. If both press the same button, you each get that amount. Otherwise, $0.

Before copying, you can take a pill that forces you to press $10.

### The source's analysis
UDT1.0's answer depends on its prior. Pressing $5 is a **consistent equilibrium**: "if you expect that's what you'll end up doing, then it is in fact what you end up doing" (source, footnote to the example). If your prior expects $5, both instances press $5, and anticipating this you prefer to take the pill — a failure of self-trust.

### What functional identity does and does not give you

**What it gives:** the two copies run the same algorithm F, so their actions are logically correlated — you cannot change your action while holding your copy's fixed. Reasoning that imagines otherwise (CDT-style independent deviation) is incoherent here.

**What it does not give:** selection between the *agreeing* profiles. Both-press-$5 satisfies functional identity perfectly — F is the constant-$5 function, both copies run it, both press $5. So does both-press-$10. Functional identity constrains the copies to the diagonal of the payoff matrix; it says nothing about *which point on the diagonal* the prior's fixed-point dynamics land on.

**The earlier version of this file claimed** the bad equilibrium is "only stable if you imagine you can change your action without changing your copy's action." That is false — the $5 equilibrium is stable *within* fully functional-identity-respecting reasoning, because UDT1.0 evaluates E[U | F(o) = a] against its prior over what F does, and a prior concentrated on $5 makes $5 self-confirming. **The prior-dependence pathology is a fixed-point selection problem, and functional identity does not touch it.**

### What actually addresses it
- **UDT1.1** (choose the whole policy at once) solves the coordination problem by brute force, but the source rejects it as violating the Vingean principle (not cognitively realistic to plan everything at once).
- **Communication** — the source's approach: before copying, think "I should press $10"; both copies recall this and press $10, "secure in the knowledge that there would be no reason for your other instance to change its mind." Communication acts as the equilibrium-selection device.

**Corrected takeaway:** functional identity rules out off-diagonal reasoning; communication (or something like it) is needed to select the good fixed point. The representation theorem framework needs an account of equilibrium selection — this is an open piece, not a solved one.

---

## Example 2: Memory Problem

### Setup
At time 1, you observe a red or green light. At time 2, you may take a pill forcing you to say "red" (or one forcing "green") for the duration. Your memory is then wiped. At time 3, you're asked what color the light was, and rewarded for a correct answer.

### The source's analysis
UDT lacks self-trust here: it takes the pill (self-modification) because that's the only way to carry the information past the memory wipe.

### Where the unfairness actually is

**Not in decision-determination.** The environment's reward depends only on the external report ("red"/"green") and the actual light color. It cannot distinguish a genuine-memory report from a pill-forced one — same external behavior, same reward. The problem *is* decision-determined in the relevant sense. (The earlier version of this file claimed the environment "distinguishes between policies based on internal mechanism" — it does not; that was a misdiagnosis.)

**In the channel asymmetry.** The source: "the pill was allowed to accomplish something which the agent's own memory was not allowed to do." The agent has a self-*modification* channel (the pill) that can carry information across the wipe, but no parallel self-*communication* channel (memory). The source's fairness condition is exactly this parallelism: "lines of communication should 'exactly parallel' lines of self-modification."

**Corrected takeaway:** the Memory Problem is outside the theorem's scope, but because it violates the **communicative-alternatives** condition, not decision-determination. This distinction matters: it shows the representation theorem needs *two* independent fairness conditions, and conflating them hides the second one. (`topics/self-trust.md` has the correct two-condition apparatus.)

---

## Example 3: Third Button

### Setup
As in Coordinated Buttons, plus a third button labeled $20. Payoffs: both press $5 → $5 each; both press $10 → $10 each; one presses $10 and the other $20 → **$20 each**; anything else → $0. You cannot randomize, and — critically — **"you cannot tell yourself to do different things depending on the color of the room (your memory will be wiped in such a case)"** (source stipulation the earlier version of this file omitted entirely).

### The source's analysis
This problem is fair by all the standards introduced so far — decision-determined, and the communication channel parallels the modification channel. Yet communication *fails to secure coordination*: if you tell yourself "press $10," then each copy, trusting that the *other* will follow the instruction, reasons that pressing $20 is better — "however, if that were true, *this would lead both copies to choose $20*," yielding $0. So UDT may still resort to the pill, and the source concludes further conditions are needed (this motivates the external/internal action distinction and the refined fairness notion).

### What the framework says, carefully

The symmetric-reasoning observation is real: "I know my copy will press $10, so I'll press $20" is incoherent under functional identity, because your copy runs the same reasoning — whatever conclusion you reach, they reach. If both copies reason symmetrically from the recommendation, the $20-defection collapses into both-press-$20 = $0, which symmetric reasoning can see coming.

But note what this argument is: it is *again* a fixed-point selection argument, and it has the same gap as in Example 1 — "we'll do the same thing, so pick the best same-thing" requires the reasoner to step outside the recommendation-trusting frame the source is analyzing. The source treats the instability as a genuine problem requiring new machinery (ruling such cases out), not as one dissolved by symmetric reasoning. The earlier version of this file declared "the representation theorem applies... yields: press $10" — that conclusion is not licensed; the honest status is that Third Button is the example showing communication + functional identity are *jointly insufficient*, which is why the source's later formal sections exist.

(Side note on the asymmetric profile: one-presses-$10/other-presses-$20 pays $20 each — better than both-press-$10. The room colors are distinct observations, so a room-conditional policy is not ruled out by functional identity as such; what the stipulation forbids is *instructing* yourself room-dependently. Whether in-room symmetric reasoning could legitimately reach the asymmetric profile is exactly the kind of question the framework currently cannot answer — it is fixed-point selection again, now over a larger set.)

---

## Synthesis: When Does Self-Trust Hold?

### The paper's approach
1. Define self-trust as non-preference for self-modification
2. Define "fair" problems: decision-determination **and** communicative alternatives (two separate conditions — see Example 2)
3. Prove: in fair problems, UDT agents have self-trust — with Third Button showing the conditions so far are still not enough

### The representation-theorem framing
1. Define "single coherent agent" via axioms (functional identity, unity, decision-determination)
2. Derive: such agents reason updatelessly
3. The examples then locate what's missing: an equilibrium-selection principle (Examples 1, 3) and the communication/modification parallelism condition (Example 2)

### The role of communication
Communication is the source's equilibrium-selection device (Example 1) — not redundant with functional identity, but the thing that does the work functional identity cannot. It acts as a "release valve" for self-modification pressure. Third Button shows the valve is not always sufficient. In the representation-theorem framing: functional identity restricts to the diagonal; communication selects a point on it; and Third Button shows selection-by-recommendation can itself be destabilized by reasoning *about* the recommendation.

---

## Implications for the Paper

The paper's structure can be reframed (this section survives from the original file):

**Sections 4-5 (Framework):** Present I/B/E as the structure we impose when attributing agency. Motivate via "agency as modeling."

**Section 6 (Instances & Communication):** "Instances" are applications of the agency model. Communication enables coordination where functional identity is insufficient — which, per the corrected analysis above, is *all* nontrivial coordination (functional identity alone never selects).

**Section 7 (Self-Trust):** Agents satisfying the axioms don't prefer self-modification *when the fairness conditions hold*; the examples calibrate exactly which conditions are needed.

**Section 8 (Following Advice):** Recommendation-following is stable only under conditions that rule out Third-Button-style reasoning about the recommendation.

---

## Open Questions

1. **The equilibrium-selection problem** (promoted; was hidden by the old "FI resolves it" claims): what principle selects among functional-identity-respecting fixed points? Communication per the source; but Third Button shows the naive version fails. This is arguably the same problem as UDT1.0's prior-dependence, and the framework does not currently solve it.
2. **When exactly does functional identity hold?** Exact copies: yes. Similar reasoning: approximately. Different algorithms: no (but communication can help).
3. **How does uncertainty about functional identity affect reasoning?** Probably: weight by probability of identity.
4. **Functional identity vs acausal trade:** there might be a spectrum from identity to simulation to prediction.
5. **Connection to logical uncertainty:** functional identity assumes you know what algorithm you're running; combining with logical uncertainty is open.

---

## Summary

1. **Coordinated Buttons:** functional identity restricts to the diagonal but cannot select the good fixed point; the prior-dependence pathology is an equilibrium-selection problem, addressed in the source by communication.
2. **Memory Problem:** unfair — but via the communication/modification channel asymmetry, *not* decision-determination. The theorem needs both fairness conditions, separately.
3. **Third Button:** the source's demonstration that communication + fairness-so-far are still insufficient; symmetric reasoning gestures at stability but is itself another unsolved selection argument.

The common thread, corrected: taking functional identity seriously eliminates one class of error (independent-deviation reasoning) and exposes the real open problem (fixed-point selection), which the representation theorem framework has not yet solved.
