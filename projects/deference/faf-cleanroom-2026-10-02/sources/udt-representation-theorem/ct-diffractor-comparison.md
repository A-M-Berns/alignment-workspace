# Communication & Trust vs Diffractor: A Careful Comparison

## The Two Frameworks

### Communication & Trust (C&T)

**Structure:** I/B/E decomposition
- **I** (Interior): Persistent state, memories
- **B** (Boundary): Decision procedure
- **E** (Environment): External world

**Information Flow:**
- Ȯ (internal observation): I → B (memories, computations)
- Ö (external observation): E → B (sense data)
- Full observation O = (Ȯ, Ö)
- Semantic Ô vs side channel Ǒ (legitimate vs illegitimate internal info)

**Policies:**
- Full policy π: O → A
- External policy π̈: Ö → Ä (what environment sees)
- Chosen policy Π* vs effective policy Π†

**Instances:** Factored by Ö (external observation)

### Diffractor's UDT1.01

**Structure:** Tree of observations
- **Contracted tree:** Plannable observations h (environmental)
- **Expanded tree:** (h, S) pairs (plannable + epistemic state)

**Information:**
- h: Plannable observations (can write lookup-table policy)
- S: Epistemic state (beliefs, computation outputs, policy guesses)

**Policies:**
- Narrow policy: h → a (on contracted tree)
- Broad policy: How to respond to (h, S) (on expanded tree)

**Instances:** Nodes (h, S) in expanded tree

## First-Pass Mapping

| C&T | Diffractor | Notes |
|-----|-----------|-------|
| Ö (external) | h (plannable) | Environmental situation |
| Ȯ (internal) | S (epistemic)? | Internal information |
| π̈ (external policy) | Narrow policy | What coordination uses |
| π (full policy) | Broad policy | What determines behavior |

**But this mapping is too simple.** The concepts don't align cleanly.

## Key Differences

### Difference 1: Source vs Tractability

**C&T distinction:** WHERE does information come from?
- Internal (Ȯ): From the interior I
- External (Ö): From the environment E

**Diffractor distinction:** CAN you plan for it?
- Plannable (h): Can write a lookup-table policy
- Unplanned (S): Affects action but can't be pre-planned

These are orthogonal!
- External observations Ö might be plannable (you can write π̈)
- Internal observations Ȯ might be unplannable (computation outputs)
- Or internal observations might be plannable (predictable memories)

### Difference 2: Determination vs Uncertainty

**C&T:** Given Ö and dynamics D_{I,B}, internal state Ȯ is *determined*.

From Agent Dynamic Constraint: (I, B) factors as (Ö, D_{I,B}).

**Diffractor:** Given h, epistemic state S is *uncertain*.

You don't know what S you'll have until you "think" (observe computation outputs).

**This is a key structural difference:**
- C&T: Uncertainty is in D (the dynamics), determinism in Ȯ given D
- Diffractor: Uncertainty is in S given h

### Difference 3: Communication Structure

**C&T:** Rich communication structure
- Interior I persists across decisions
- Instances at different Ö can communicate through shared Ȯ
- Communication is how coordination happens

**Diffractor:** Minimal communication structure
- No explicit persistent state
- Coordination through common algorithm, not information sharing
- Different (h, S) nodes don't explicitly communicate

### Difference 4: Legitimacy

**C&T:** Explicit legitimacy distinction
- Ô (semantic): Information you're "supposed to" receive
- Ǒ (side channel): Modifications to your behavior

This captures when internal information is legitimate vs when it's manipulation.

**Diffractor:** No explicit legitimacy distinction
- All S is treated symmetrically
- Implicit assumption that S is "honest" (your actual beliefs)

## A Deeper Analysis

### What is Ȯ (internal observation)?

In C&T, Ȯ includes:
1. **Memories:** Results of past processing, stored in I
2. **Semantic content Ô:** What you're supposed to learn from I
3. **Side channel Ǒ:** Modifications that change your behavior

This is a heterogeneous category - it includes both "legitimate information" and "procedure modification."

### What is S (epistemic state)?

In Diffractor, S includes:
1. **Beliefs about the world:** Probabilities, expected utilities
2. **Computation outputs:** Results of thinking, inference
3. **Policy guesses:** Your beliefs about your own behavior

This is an epistemically homogeneous category - it's all "your beliefs."

### The Mapping, Refined

| C&T Concept | Diffractor Analog | Notes |
|-------------|------------------|-------|
| Ö (external obs) | h (plannable) | Environmental history |
| Ô (semantic) | S (epistemic state) | Legitimate internal info |
| Ǒ (side channel) | *no direct analog* | Illegitimate modification |
| I (interior) | *implicit* | How S evolves over time |
| D_B (boundary dynamic) | The algorithm | How you turn S into actions |

**Key insight:** The side channel Ǒ has no direct analog in Diffractor's framework. C&T is explicitly modeling something Diffractor leaves implicit.

## The Dynamics Question

### C&T: Policy determined by D_B

The boundary dynamic D_B encodes "how you decide." Given D_B, the policy π is determined.

Uncertainty about your policy = uncertainty about D_B.

### Diffractor: Action computed from S

You run an algorithm (UDT1.01) on your epistemic state S to get an action.

Uncertainty about your action = uncertainty about S.

### Reconciliation

These are **dual perspectives on the same phenomenon:**

**C&T perspective:** "I don't know my procedure D_B exactly, but once I know D_B and observe O, my action is determined."

**Diffractor perspective:** "I know my procedure (UDT1.01), but I don't know my epistemic state S until I think. Once I know S, my action is determined."

The uncertainty is **located differently**:
- C&T puts uncertainty in D_B (mechanism)
- Diffractor puts uncertainty in S (epistemics)

But they're describing the same phenomenon: self-uncertainty leading to action-uncertainty.

## Instances: A Crucial Difference

### C&T Instances

Instances are factored by Ö (external observation).

Two moments with different Ö are different instances.
Two moments with same Ö but different Ȯ are... the same instance? Different states of the same instance?

The paper seems to treat instances as characterized by Ö, with Ȯ being "internal details."

### Diffractor Instances

If we interpret (h, S) pairs as "instances":

Two nodes with different h are different instances.
Two nodes with same h but different S are different instances too!

This is a finer-grained notion of instance.

### Reconciliation

**A C&T "instance" (at Ö) corresponds to a FAMILY of Diffractor nodes:**

{(h, S) : h corresponds to Ö sequence, S varies}

Within a C&T instance:
- Different Ȯ values (different internal states)
- Correspond to different S values in Diffractor
- These are "sub-instances" or "epistemic variants"

**Communication in C&T** allows coordination across instances (different Ö).
**No explicit communication in Diffractor** between (h, S) nodes.

But coordination in Diffractor happens through the **common algorithm** - all nodes run UDT1.01.

## The Communication Structure

### C&T Communication

How do instances at different Ö coordinate?

Through the interior I:
1. Instance at Ö₁ takes internal action Ȧ₁
2. This modifies I
3. Instance at Ö₂ receives internal observation Ȯ₂ reflecting this
4. Coordination achieved through shared memory

**Communication = sharing information through I.**

### Diffractor "Communication"

How do nodes at different (h, S) coordinate?

Through the common algorithm:
1. All nodes agree to run UDT1.01
2. Each node, given its S, computes the UDT1.01 action
3. The actions are coordinated because the algorithm accounts for cross-node effects

**No explicit information sharing, but implicit coordination through algorithmic agreement.**

### Synthesis

**C&T communication could be modeled in Diffractor's framework as:**

A mechanism that correlates S values across h values.

If I stores information from h₁ that affects S at h₂, that's "communication" in Diffractor's implicit sense.

**Diffractor's algorithmic coordination could be modeled in C&T as:**

Agreement on D_B (the boundary dynamic).

If all instances have the same D_B (run the same algorithm), they coordinate even without explicit communication.

## The Legitimacy Question

### C&T: Semantic vs Side Channel

Ô = semantic observation = legitimate input to decision-making
Ǒ = side channel = illegitimate modification of procedure

**Why does this matter?**

The chosen policy Π* is what you WOULD do without modification.
The effective policy Π† is what you ACTUALLY do (possibly after modification via Ǒ).

Self-trust = preferring Π* = Π† (no modification is beneficial).

The side channel Ǒ is what can cause Π† ≠ Π*.

### Diffractor: No Explicit Legitimacy

All S is treated the same - no "legitimate" vs "illegitimate" epistemic states.

But implicitly:
- S should be your "honest" beliefs
- If someone could manipulate S (make you believe false things), that's bad
- This would be like a "side channel" in C&T

### Synthesis

**The side channel Ǒ in C&T corresponds to "manipulation of S" in Diffractor.**

Legitimate reasoning: You compute, observe S, act according to UDT1.01.
Illegitimate manipulation: Someone modifies your S to make you act differently.

**C&T models this explicitly; Diffractor leaves it implicit.**

To fully synthesize:
1. Add a legitimacy distinction to Diffractor: S_semantic vs S_manipulated
2. Non-interference = only using S_semantic, not manipulating others' S

## The Complete Synthesis

### Structural Layer (from C&T)

- I/B/E decomposition: Agent has interior, boundary, and environment
- Information flow: Internal/external observations and actions
- Dynamics: How components interact
- Communication: Through the interior I

### Epistemic Layer (from Diffractor)

- Plannable vs unplanned: What can you write a policy for?
- Epistemic states: Your beliefs at each plannable situation
- Algorithmic coordination: Agreement on how to use epistemic states

### Combined Framework

**Components:**
- Plannable situation h ≈ External observation Ö
- Epistemic state S ≈ Semantic observation Ô (legitimate internal info)
- Side channel Ǒ ≈ Manipulation of S
- Interior I ≈ Mechanism correlating S across h

**Policies:**
- Narrow/external policy: h → a (what coordination uses)
- Broad/full policy: (h, S) → a (what actually determines behavior)
- Chosen policy: What you'd do with honest S
- Effective policy: What you actually do (possibly with manipulated S)

**Instances:**
- Coarse-grained: One per h (C&T style)
- Fine-grained: One per (h, S) (Diffractor style)
- Communication: Coarse instances share info through I
- Coordination: Fine instances coordinate through common algorithm

**Legitimacy:**
- Self-trust: Chosen policy = effective policy
- Non-interference: Don't manipulate others' S (side channel)
- Communication ≠ manipulation: Sharing info is OK; forcing conclusions is not

## Open Questions

1. **How exactly does I/memory work in Diffractor's framework?**
   - Is it implicit in how h evolves?
   - Or does S include memories?

2. **What determines the plannable/unplanned boundary?**
   - C&T has a structural answer (Ö from E vs Ȯ from I)
   - Diffractor has a tractability answer (what you can plan for)
   - Are these the same in practice?

3. **How should we handle the side channel formally?**
   - C&T has Ǒ but doesn't fully formalize its role
   - Diffractor ignores it
   - A complete theory needs to address manipulation

4. **What's the relationship between D_B and S?**
   - D_B determines how you process observations
   - S is your epistemic state after processing
   - Is S determined by D_B, or is there genuine uncertainty?

5. **How does communication affect the plannable/unplanned boundary?**
   - If instances can communicate, does more become plannable?
   - Or does communication just correlate unplanned states?

## Summary

**C&T contributes:**
- Structural clarity (I/B/E, information flow)
- Communication mechanism (through I)
- Legitimacy distinction (semantic vs side channel)
- Instance definition (factored by Ö)

**Diffractor contributes:**
- Epistemic clarity (plannable vs unplanned)
- Computational approach (algorithm + epistemic state)
- Coordination mechanism (common algorithm)
- Optimality results (UDT1.01 is universally locally optimal)

**The synthesis:**
- Use C&T structure for the "ontology"
- Use Diffractor epistemics for the "methodology"
- Map Ö ↔ h, Ô ↔ S, Ǒ ↔ manipulation
- Communication (C&T) complements algorithmic coordination (Diffractor)

**The key insight:** They're modeling the same phenomenon from different angles:
- C&T: Where does information come from? (structure)
- Diffractor: What can you plan for? (tractability)

A complete theory needs both.
