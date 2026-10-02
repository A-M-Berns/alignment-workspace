# Presentation Outline: A Representation Theorem for Updateless Decision Theory

## Title Slide
**A Representation Theorem for UDT**
*or: What "Single Coherent Agent" Really Means*

The author

---

## Part 1: The Problem (5 min)

### Slide: Decision Theory Disagreements
- CDT, EDT, UDT all say "maximize expected utility"
- They disagree about how to compute E[U | action = a]
- CDT: causal conditioning (do-operator)
- EDT: evidential conditioning
- UDT: policy/algorithmic conditioning

### Slide: The Meta-Question
- Why condition one way rather than another?
- Previous work: analyze UDT, prove properties
- This work: **derive** UDT from basic axioms about agency

### Slide: The Goal
A representation theorem:
> If you model X as a **single coherent agent** with utility U, then X reasons updatelessly.

UDT isn't one option among many - it's what "single coherent agent" *means*.

---

## Part 2: Agency as Modeling (10 min)

### Slide: The Teleological vs Mechanistic Prediction
Two ways to predict a system's behavior:
1. **Mechanistic**: Given its physical constitution, what will it do?
2. **Teleological**: Given its goals, what will it do?

Agency attribution = commitment to (2) being the better model.

### Slide: What Does Agency Attribution Look Like?
When we say "X is an agent with utility U":
- We identify a boundary (X vs environment)
- We identify observations and actions (X's interface)
- We predict: X's actions optimize U given observations

### Slide: The I/B/E Framework
- **I**nterior: internal state, memory
- **B**oundary: decision procedure, I/O
- **E**nvironment: everything else

Key insight: This structure is in the **map**, not the territory. It's how we model something when we treat it as an agent.

### Slide: What are "Instances"?
Classic view: Instances are parts of the agent (time-slices, copies, etc.)

New view: **Instances are applications of the agency model.**

If I apply the model "X optimizes U" at time 1 and time 2, those are two "instances" - two contexts where I'm using the same model.

---

## Part 3: The Conditioning Question (10 min)

### Slide: What Does "My Action is a" Mean?
When computing E[U | my action is a], what are we conditioning on?

- CDT: A surgical intervention that sets my action to a
- EDT: Evidence that my action is a (updating all beliefs)
- UDT: My **algorithm/policy** maps my observation to a

### Slide: Functional Identity
If I model myself as implementing algorithm F:
- My action IS F(o)
- "My action is a" MEANS "F(o) = a"
- This is a fact about F, which applies to all instances of F

### Slide: Why UDT Conditioning?
If you have functional identity + unity (all instances run F):

1. "My action is a" means "F(o) = a"
2. "F(o) = a" constrains F, affecting other outputs
3. Other outputs of F affect the policy
4. The policy affects utility (by decision-determination)

Therefore: condition on the algorithmic fact, not just the local action.

### Slide: Why NOT CDT Conditioning?
CDT imagines: "What if I surgically set my action to a, without changing anything else?"

But if I **am** algorithm F, there's no way to change my action without changing F.

CDT conditioning is incoherent for an agent with functional identity.

---

## Part 4: The Three Arguments (10 min)

### Slide: Argument 1 - Decision-Determination
"Fair" problems: environment responds to policy, not mechanism.

If only the policy matters, policies are the natural unit of analysis.

Evaluating policies as wholes → updateless reasoning.

### Slide: Argument 2 - Functional Identity
You model yourself as algorithm F.
You know other instances run F.
Correct conditioning accounts for this.

"My action is a" → "F(o) = a" → implications for all of F → UDT conditioning.

### Slide: Argument 3 - Parsimony
What's the simplest model of "single agent with utility U"?

- Updateful: Multiple separate optimizations, somehow connected
- Updateless: One optimization with multiple inputs/outputs

The updateless model is simpler. (Occam's razor for agency attribution.)

### Slide: The Common Thread
All three arguments converge:

**If you take "single coherent agent" seriously, you get updateless reasoning.**

---

## Part 5: The Formal Theorem (10 min)

### Slide: The Key Concept - Cross-Situation Dependence
When does this matter? When utility depends on the **pattern** of actions across situations.

**Cross-situation dependence:** Your action at situation s affects utility not just directly, but via how it correlates with actions at other situations.

Examples:
- Newcomb: Predictor responds to your policy
- Coordination: Your copy does what you do
- Commitment: Your future self trusts/distrusts you

### Slide: Split vs Unified Models
**Split model (EDT-style):** Each situation optimizes independently.
- Ask: "Given I'm in s, what should I do?"
- Multiple separate optimizations

**Unified model (UDT-style):** One optimization over the whole policy.
- Ask: "What policy should I have?"
- Single coherent optimization

**Key result:** These agree when no cross-situation dependence. They diverge when there IS dependence.

### Slide: Axioms
1. **(Unity)** The agent is a SINGLE optimizer, not separate optimizers per situation
2. **(Cross-Situation)** Utility has cross-situation dependence
3. **(Decision-Determination)** Environment responds to policy, not mechanism
4. **(Rationality)** Agent maximizes expected utility

### Slide: Theorem Statement
**Theorem.** Under Axioms 1-4, the agent's choice at observation o is:

$$a^* = \arg\max_a \mathbb{E}[U \mid \pi(o) = a]$$

This is the UDT formula: condition on "my policy maps o to a."

### Slide: Proof Sketch
- By (1), there's one policy π being optimized
- By (4), π maximizes E[U | π]
- By (2), E[U | π] depends on the whole policy, not just local actions
- By (3), the policy is what matters (not how it's computed)
- Therefore: each π(o) is chosen as part of the globally optimal policy

### Slide: The Burden of Proof Reversal
Classical framing: "Why group decision points?"

New framing: "Why SPLIT decision points?"

When you attribute agency, you're modeling a SINGLE entity. Splitting into separate optimizers requires justification.

**The unified model is the default.** The split model requires extra structure.

---

## Part 6: Reflective Stability (5 min)

### Slide: Connection to Self-Trust
Original motivation: When does an agent avoid self-modification?

**Claim:** An agent satisfying the axioms is reflectively stable.

Why? The agent chooses the optimal policy. Given a chance to change policies, it prefers not to. (That's what "optimal" means.)

### Slide: Communication as Release Valve
But coordination problems can pressure self-modification.

Solution: Communication between instances enables coordination without modification.

If you can achieve the same outcome by communicating, no pressure to modify.

---

## Part 7: Open Questions & Future Work (5 min)

### Slide: Logical Uncertainty
Agent "knows" its algorithm but is uncertain about outputs.
How does this work formally?
(Deep problem in decision theory)

### Slide: Imperfect Functional Identity
What if instances are similar but not identical?
(Realistic for humans, approximate copies)
How does the framework degrade gracefully?

### Slide: Self-Reference
Agent implements F. Agent also chooses actions.
F is defined by the choices. Choices defined by reasoning about F.
The loop is not vicious, but needs careful treatment.

### Slide: Where Does the Prior Come From?
The axioms include a probability distribution P.
Is this part of agency attribution?
Or derived from something more basic?

---

## Conclusion

### Slide: Summary
1. Agency attribution = modeling something as optimizing a utility function
2. "Single agent" across situations = unified algorithm/policy
3. Correct conditioning for such agents = algorithmic conditioning
4. This is UDT

**Representation theorem:** Axioms of coherent agency → UDT

### Slide: The Takeaway
UDT is not a peculiar decision theory for peculiar problems.

UDT is what **agency** means when you take it seriously.

---

## Appendix: Examples

### Slide: Coordinated Buttons
Before copying: "I should press $10"
After copying: both remember this, both press $10
Communication enables coordination without self-modification.

### Slide: Why This Isn't Trivial
CDT agent also "knows it's an algorithm"
But CDT doesn't propagate the conditioning correctly
CDT imagines surgical interventions that are incoherent with self-model

### Slide: Newcomb's Problem
Predictor responds to algorithm, not just this instance's action.
Functional identity: my algorithm affects prediction.
UDT one-boxes; this is correct conditioning.

---

## Timing Notes

- Part 1 (Problem): 5 min
- Part 2 (Agency as Modeling): 10 min
- Part 3 (Conditioning): 10 min
- Part 4 (Three Arguments): 10 min
- Part 5 (Formal Theorem): 10 min
- Part 6 (Reflective Stability): 5 min
- Part 7 (Open Questions): 5 min
- Conclusion: 5 min

**Total: ~60 min** (adjust based on actual slot)
