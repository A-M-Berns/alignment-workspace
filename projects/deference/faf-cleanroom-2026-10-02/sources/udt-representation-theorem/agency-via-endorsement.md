# Agency via Endorsement: A Condensation-Theoretic Treatment

## Setup: Bipartite Agent-Environment Model

We work with a probability space (Ω, P). We have two primary random variables:

- **A** : Ω → R_A — the "agent" (what the agent controls/is)
- **E** : Ω → R_E — the "environment" (everything external)

Under condensation assumptions, we can reify the information-theoretic relationships:

### Condensation Variables

**Boundary (mutual information):**
- **B = A ∨ E** — the common information, finest variable that's a function of both A and E
- H(B) = I(A; E)
- B is a subvariable of both A and E

**Policy (agent's residual):**
- **Π** — the condensation variable for H(A | E)
- Satisfies: H(A | Π, E) = 0, and Π is independent of E in support
- A factors as (B, Π) where B = A ∨ E
- Intuitively: Π is what the agent "brings to the table" beyond what's shared with environment

**Environment's residual:**
- **Ξ** — the condensation variable for H(E | A)
- Satisfies: H(E | Ξ, A) = 0, and Ξ is independent of A in support
- E factors as (B, Ξ)

### The Factorization Picture

```
        A = (B, Π)          E = (B, Ξ)
            ↓                   ↓
            B ←───────→ B
       (boundary)        (boundary)
```

The world Ω factors as (Π, B, Ξ) where:
- Π, B, Ξ are mutually independent in support
- A = (B, Π) and E = (B, Ξ)
- The boundary B is the "interface" — the shared information

---

## Endorsement-Based Agency

Following "Meaning & Agency", we define agency through the lens of an **observer** (Alice) attributing agency to a **system** (Bob).

### The Observer's Perspective

Alice has:
- Beliefs P₁ over the sample space Ω
- A choice function C₁ (how Alice would optimize)
- Access to some variables as "observable" — she can condition on their values

Alice observes the system and asks: "Is this system optimizing something?"

### Belief Endorsement (Simplest Case)

**Definition (Belief Endorsement):** P₁ belief-endorses Π with respect to target X if:

$$P_1(X \mid \Pi = \pi) = f_\pi(X)$$

where f_π is the "belief about X" encoded by policy π, and Alice adopts this belief upon learning the policy.

More precisely: if we think of each π ∈ R_Π as encoding a belief about X, then P₁ endorses Π if conditioning on Π = π gives Alice the belief that π encodes.

This is relevant when the "optimization target" is epistemic — the system is trying to have accurate beliefs.

---

## Selection Endorsement

**Setup:**
- Let V be a random variable we interpret as the system's "output" or "choice"
- Let U_sel : R_V → ℝ be a **pure utility function** (depends only on the choice, not the world)

**Definition (Selection Endorsement):** Alice selection-endorses the system (with policy Π) as optimizing U_sel if:

$$C^1_{U_{sel}, P_1}(R_V \mid \Pi = \pi) = v_\pi$$

where v_π is the value of V determined by policy π.

In words: If Alice were trying to optimize U_sel, and she learned the system's policy is π, she would choose the same action that π chooses.

### Formal Expansion

Let C be argmax for simplicity. Then selection endorsement means:

$$\arg\max_{v \in R_V} E_{P_1}[U_{sel}(v) \mid \Pi = \pi] = v_\pi$$

But U_sel(v) doesn't depend on ω, so:

$$\arg\max_{v \in R_V} U_{sel}(v) = v_\pi$$

This is trivial unless we interpret it correctly: the point is that **v_π must be optimal**, i.e., the system's policy always picks U_sel-optimal actions.

### Selection Endorsement with Observation Structure

More interesting: suppose the system observes O (a subvariable of E) and chooses action Act. The policy is π : R_O → R_{Act}.

**Definition (Selection Endorsement with Observations):** Alice selection-endorses (Π, O, Act) as optimizing U_sel : R_{Act} → ℝ if for all o ∈ R_O:

$$\arg\max_{a \in R_{Act}} U_{sel}(a) = \pi(o)$$

This says: regardless of observation, the policy picks the U_sel-optimal action.

This is only non-trivial if U_sel depends on o — but then it's not a pure function of Act. So pure selection endorsement is essentially: "the system always outputs the same optimal thing."

---

## Control Endorsement

**Setup:**
- Let V be the system's output
- Let U_ctrl : Ω × R_V → ℝ be an **impure utility function** (depends on world and choice)

Or equivalently, since we're conditioning on policy:
- U_ctrl : R_Ξ × R_B × R_V → ℝ — utility depends on environment's residual, boundary, and choice

**Definition (Control Endorsement):** Alice control-endorses the system (with policy Π) as optimizing U_ctrl if:

$$C^1_{U_{ctrl}, P_1}(R_V \mid \Pi = \pi) = v_\pi$$

where v_π is the value of V determined by policy π (as a function of boundary B).

### Formal Expansion with Condensation Structure

The system's policy Π determines a function π : R_B → R_V (mapping boundary values to outputs).

Control endorsement means: for each π,

$$\arg\max_{v : R_B \to R_V} E_{P_1}\left[\sum_{b \in R_B} \mathbf{1}[B=b] \cdot U_{ctrl}(\Xi, b, v(b)) \mid \Pi = \pi\right] = \pi$$

Since Π is independent of (B, Ξ) in support, conditioning on Π = π doesn't change the distribution of (B, Ξ). So:

$$\arg\max_{v : R_B \to R_V} E_{P_1}\left[U_{ctrl}(\Xi, B, v(B))\right] = \pi$$

This is interesting! It says: **the policy π that the system implements is exactly the policy Alice would choose** if she were optimizing U_ctrl.

### Pointwise Control Endorsement

We can also state this pointwise over boundary values:

$$\arg\max_{a \in R_V} E_{P_1}\left[U_{ctrl}(\Xi, b, a) \mid B = b\right] = \pi(b) \quad \forall b \in R_B$$

This is: at each boundary value b, the policy's action π(b) is what Alice would choose.

---

## The UDT Connection

In the UDT representation theorem, we have:
- Observations O (part of boundary B in our framing)
- Actions Act (what the policy chooses)
- Global utility U : Ω → ℝ

The UDT formula says:
$$\pi(o) = \arg\max_a E[U \mid \Pi(o) = a]$$

### Translating to Endorsement Language

Let Alice's beliefs P₁ be the agent's prior. Let U_ctrl(ω, a) = U(ω) when the action at observation o is a.

Then UDT says: for all observations o,
$$\arg\max_a E_{P_1}[U \mid \Pi(o) = a] = \pi(o)$$

**Claim:** An agent following UDT is control-endorsed by its own prior.

**Why:** The UDT agent, at each observation, chooses the action that maximizes expected utility from the prior's perspective. This is exactly what control endorsement requires: Alice (= the prior) would make the same choice.

---

## Selection vs Control: The Key Distinction

### Selection (Pure U)

- U_sel : R_V → ℝ depends only on the output
- The optimal output is fixed regardless of world-state
- Example: "Output the largest number" — the system just needs to output ∞ (or max of range)
- **No beliefs required** — the system doesn't need to know anything about the world

### Control (Impure U)

- U_ctrl : Ω × R_V → ℝ depends on world and output
- The optimal output varies with world-state
- Example: "Output a prediction of X" — the system needs beliefs about X
- **Beliefs required** — the system must track world-state to optimize

### The Condensation Perspective

In selection: the policy Π can be trivial (constant function) and still be endorsed.

In control: the policy Π must **encode information about E** to be endorsed. Specifically, the policy must encode enough to compute the optimal action at each boundary state.

This suggests: **control endorsement implies the policy has structure** — it's not arbitrary, but reflects optimization under uncertainty.

---

## Endorsement with Explicit Boundary Structure

Let's be fully explicit with our condensation variables.

**Setup:**
- (Ω, P) probability space
- A, E random variables with A ∨ E = B (boundary)
- A factors as (Π, B) with Π the policy (condensation variable for H(A|E))
- E factors as (Ξ, B) with Ξ the environment's residual

**The agent's "choice" is:** given B = b, output some value. The policy Π determines this: Π = π means "use function π : R_B → R_A".

**Utility:** U : Ω → ℝ, which we can write as U : R_Π × R_B × R_Ξ → ℝ.

**Definition (Full Control Endorsement):** Observer with beliefs P₁ control-endorses Π as optimizing U if:

$$\forall \pi \in R_\Pi : \quad \pi = \arg\max_{f : R_B \to R_A} E_{P_1}[U(f, B, \Xi) \mid \Pi = \pi]$$

Under independence (Π ⊥ (B, Ξ)):

$$\forall \pi \in R_\Pi : \quad \pi = \arg\max_{f : R_B \to R_A} E_{P_1}[U(f, B, \Xi)]$$

This means: **every policy in the support is optimal**. The distribution over policies P₁(Π = π) can have any shape, but each π in the support must be an optimizer.

---

## Conditional Endorsement and Levels of Trust

Following "Meaning & Agency", we can partially order systems by how much they're endorsed.

**Definition (Conditional Control Endorsement):** P₁ endorses Π₂ given Π₁ (both as optimizing U) if:

$$C^1_{U, P_1}(R_V \mid \Pi_1 = \pi_1, \Pi_2 = \pi_2) = v_{\pi_2}$$

Alice still endorses Π₂'s choice even after learning Π₁'s choice.

If Alice endorses Π₂ given Π₁ but not vice versa, she trusts Π₂ more.

---

## Summary: The Definitions

Let (Ω, P) be a probability space with A, E, B = A ∨ E, and Π the condensation variable for H(A|E).

**Selection Endorsement:** P₁ selection-endorses Π as optimizing U_sel : R_A → ℝ if every π in support(Π) satisfies:
$$\pi(b) \in \arg\max_a U_{sel}(a) \quad \forall b$$

**Control Endorsement:** P₁ control-endorses Π as optimizing U_ctrl : Ω → ℝ if every π in support(Π) satisfies:
$$\pi = \arg\max_f E_{P_1}[U_{ctrl}(f(B), B, \Xi)]$$

**UDT as Self-Endorsement:** An agent using UDT with prior P is control-endorsed by P as optimizing its utility U:
$$\pi^{UDT}(b) = \arg\max_a E_P[U \mid \text{action at } b \text{ is } a]$$

The representation theorem goal: show that under appropriate conditions (decision-determination, condensation, etc.), **any control-endorsed policy must satisfy the UDT formula**.
