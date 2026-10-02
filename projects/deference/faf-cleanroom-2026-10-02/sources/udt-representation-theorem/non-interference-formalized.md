# Non-Interference Among Instances: Formal Treatment

## The Non-Interference Principle

**Informal:** An instance X_o doesn't try to override or modify other instances X_o'.

**Why this matters:**
- It's the core of self-trust
- It distinguishes "coordination" from "control"
- It's what makes the multi-agent view coherent

## Classical vs. Multi-Agent Framing

### Classical UDT Framing

**One policy, multiple applications:**
- There's a single π: O → A
- Each instance is an "application" of π
- Non-interference is automatic: there's nothing to interfere WITH
- "Self-trust" means not wanting to change π

### Multi-Agent Framing

**Multiple deliberators, coordinated by contract:**
- Each X_o is a genuine deliberator with its own "mind"
- The "policy" emerges from their coordinated decisions
- Non-interference is a CHOICE: X_o could try to override X_o', but doesn't
- "Self-trust" means respecting other instances' deliberative authority

## What Does "Interference" Mean?

### In the Paper's Framework

The paper distinguishes:
- **Chosen policy Π*:** What the agent would do without modification
- **Effective policy Π†:** What the agent actually does (possibly after modification)

**Self-modification:** Actions that change Π† to differ from Π*.

**Interference** = self-modification that affects other instances:
- X_o takes action that changes how X_o' will behave
- X_o overrides X_o' 's deliberation

### Types of Interference

1. **Direct modification:** X_o changes X_o' 's algorithm/memory
2. **Commitment device:** X_o constrains X_o' 's options (like Ulysses and the mast)
3. **Information manipulation:** X_o gives X_o' false information to change their decision
4. **Side-channel manipulation:** X_o exploits non-semantic aspects of the interface

### Non-Interference as a Constraint

**Non-interference condition:** X_o takes only actions consistent with X_o' implementing Π* (the chosen policy).

This means:
- No direct modification of other instances
- No commitment devices that override deliberation
- No information manipulation
- No side-channel exploitation

## Why Respect Non-Interference?

### Argument 1: Contractual Obligation

The instances agreed to a contract. Part of the contract is: "We each respect each other's deliberative authority."

Breaking this is defection. It undermines the whole coordination structure.

### Argument 2: Futility (Under Functional Identity)

If X_o and X_o' run the same algorithm:
- Any reasoning X_o uses to justify interference, X_o' could also use
- If interference is "allowed," it's allowed for everyone
- Universal interference breaks coordination

So non-interference is the stable equilibrium.

### Argument 3: Epistemic Humility

X_o might think X_o' is making a mistake. But:
- X_o' has information X_o doesn't (different observation)
- X_o' might be reasoning correctly given that information
- X_o should be humble about second-guessing X_o'

Non-interference follows from respecting X_o' 's epistemic position.

### Argument 4: The Representation Theorem

If X_o interferes with X_o', the "policy" is no longer coherent:
- What X_o does depends on opportunity to interfere
- The environment responds to this mess, not to a clean policy
- Decision-determination fails

Non-interference is required for the representation theorem to apply.

## Formal Characterization

### The Paper's Approach

**Definition (from paper):** The agent has self-trust if it never strictly prefers modification opportunities over non-modification.

Formally: For all modification opportunities M,
E[U | Π† = Π*] ≥ E[U | Π† ≠ Π*]

The agent does at least as well by sticking with Π* as by modifying.

### The Multi-Agent Approach

**Definition:** The system of instances {X_o} is non-interfering if each X_o's action is consistent with all other X_o' implementing their chosen actions.

Formally: Let a_o = X_o's chosen action (from deliberation).
Let a'_o = X_o's actual action (possibly including interference effects).

Non-interference: a'_o = a_o for all o.

**Equivalently:** No instance takes actions that cause other instances to deviate from their deliberated choices.

### The Relationship

The paper's self-trust: No preference for self-modification.
The multi-agent non-interference: No actual interference.

**Connection:** Under rationality, no preference implies no actual. If there's no benefit to interfering, a rational agent won't interfere.

## When Is Interference Tempting?

### Coordination Failure

If X_o expects X_o' to make a "bad" decision, X_o might want to intervene.

**Example:** Coordinated Buttons with pessimistic prior.
- X_o (in red room) expects X_o' (in green room) to press $5
- X_o thinks: "If I could make X_o' press $10, we'd both be better off"
- Temptation to interfere

**Resolution:** Under functional identity, X_o can think: "If I would press $10, so would X_o' (same algorithm). No need to interfere; just press $10."

### Time Inconsistency

X_now might disagree with what X_future will do.

**Example:** Ulysses and the Sirens.
- X_now (before hearing) wants to sail past safely
- X_future (hearing the Sirens) will want to steer toward them
- X_now is tempted to constrain X_future (rope to mast)

**Resolution in multi-agent framework:**
- Is this legitimate renegotiation or illegitimate interference?
- Key question: Did X_future consent to the constraint?
- If "past self constraining future self" is part of the contract, it's legitimate
- If not, it's interference

### Asymmetric Information

X_o might have information X_o' doesn't, suggesting X_o' will err.

**Example:**
- X_o observes that the environment is hostile
- X_o' doesn't know this and will act as if friendly
- X_o is tempted to modify X_o' 's behavior

**Resolution:**
- Communication, not modification
- X_o should TELL X_o' about the hostile environment
- X_o' then decides with full information
- This respects X_o' 's deliberative authority

## The Communication Alternative

### Principle

Whenever X_o is tempted to interfere with X_o', there should be a communication alternative that achieves the same goal without interference.

**Communication:** X_o sends information to X_o', X_o' updates and decides.
**Interference:** X_o changes X_o' 's behavior directly.

### Formal Condition (from Paper)

**Communicative alternative:** For any modification opportunity, there exists a communicative action that achieves the same expected utility.

If communicative alternatives always exist, then:
- Interference is never necessary
- Rational agents will prefer communication (respects autonomy, same outcome)
- Non-interference is satisfied

### The Paper's Theorem

**Theorem (Self-Trust):** Under decision-determination + communicative alternatives, the agent has self-trust.

**Translation:** If the environment responds to policies (decision-determination), and communication can achieve anything modification can (communicative alternatives), then there's no reason to modify.

## Multi-Agent Interpretation of the Theorem

### The Setup
- Instances {X_o} with shared contract
- Decision-determined environment (responds to joint policy)
- Communication channels between instances

### The Claim
If communicative alternatives exist, then non-interference is optimal.

### The Argument
1. Interference changes the effective policy
2. Under decision-determination, what matters is the policy
3. Communication can change the policy (by changing other instances' decisions)
4. So communication achieves whatever interference would achieve
5. Communication is preferable (respects autonomy, same outcome)
6. Therefore, rational instances don't interfere

## Radical Probabilist Refinement

### The Subtlety

In the radical probabilist framework, instances can "change their minds" in ways not forced by evidence.

**Question:** Is changing your mind about the contract a form of interference?

### Resolution

**Legitimate change of mind:** X_o reflects on the contract and concludes it should be updated. X_o communicates this to other instances. If they agree, the contract is renegotiated.

**Illegitimate interference:** X_o unilaterally decides to ignore the contract. X_o doesn't communicate or seek agreement. X_o just acts differently.

**The difference:** Legitimate change goes through the "amendment" process. Illegitimate change is defection.

### The Contract Must Allow Amendment

A rigid contract that can never be changed is a bad contract:
- Circumstances change
- Instances learn new things
- What seemed optimal before might not be optimal now

**Solution:** The contract includes an amendment process.
- Any instance can propose changes
- Changes require agreement (or at least non-objection)
- Unilateral change is defection

## Summary

**Non-interference:** Instances don't override each other's decisions.

**Why it holds:**
- Contractual obligation (we agreed not to)
- Futility (under functional identity, interference is self-undermining)
- Epistemic humility (respect others' epistemic position)
- Representation theorem (required for coherent policy)

**The communication alternative:**
- Whenever interference is tempting, communication achieves the same goal
- Communication respects autonomy; interference doesn't
- Rational agents choose communication

**Radical probabilist refinement:**
- Changing your mind is OK if it goes through the amendment process
- Unilateral change without communication is defection

**The result:** A system of instances that coordinate through agreement and communication, without any instance dominating the others. This is the multi-agent picture of UDT.
