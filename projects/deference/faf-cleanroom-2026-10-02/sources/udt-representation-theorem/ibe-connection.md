# Connecting the Representation Theorem to the I/B/E Framework

## Goal

Show how the representation theorem framework relates to the I/B/E (Interior/Boundary/Environment) decomposition in the original paper. The key claim: the I/B/E framework is the mathematical structure we impose when attributing agency, and the representation theorem follows from taking this attribution seriously.

## The I/B/E Framework (Summary)

From the original paper:

**Three components:**
- **I (Interior):** Persistent state (memories, computations)
- **B (Boundary):** Decision procedure (input/output mapping)
- **E (Environment):** Everything external to the agent

**Information flow:**
- O = (Ȯ, Ö) : observations (internal + external)
- A = (Ȧ, Ä) : actions (internal + external)

**Dynamics:**
- D_I : how interior processes inputs
- D_B : the agent's decision rule
- D_E : how environment processes actions

**Policy:**
- Full policy π : O → A
- Effective policy Π† : what the agent actually implements
- Chosen policy Π* : what would be implemented without modification
- External policy Π̈ : how the agent appears externally

## Reinterpreting I/B/E as Modeling Choice

**Claim:** The I/B/E decomposition is not discovered in the world; it's imposed when we model something as an agent.

**The modeling step:**
1. We observe a system S
2. We decide to model S as an "agent with utility U"
3. We draw the I/B/E boundaries to make this modeling work
4. The boundaries define what counts as "observation," "action," "policy"

**This is agency attribution:**
- We're not claiming S "really is" an agent in some metaphysical sense
- We're claiming the teleological model (S optimizes U) predicts S's behavior well
- The I/B/E structure is the mathematical scaffolding for this model

## How the Representation Theorem Uses I/B/E

**The representation theorem's setup maps to I/B/E:**

| Representation Theorem | I/B/E Framework |
|------------------------|-----------------|
| Situations S | Observation space O |
| Actions A | Action space A |
| Policy π: S → A | Full policy π: O → A |
| Cross-situation dependence | Policy-dependent environment response |
| Decision-determination | E responds to Π, not to D_B's internals |

**Key correspondence:**
- "Situation" in the theorem = "observation" in I/B/E
- Both define the finest grain at which the agent can condition

## The Unity Axiom and Effective Policy

**In the representation theorem:** The unity axiom says the agent is a single optimizer with one policy.

**In I/B/E terms:** The agent has a single effective policy Π†. All "instances" (appearances at different observations) are outputs of this same policy.

**The connection:**
- Unity ↔ single Π†
- Split model ↔ treating each Π†(o) as a separate optimizer
- Unified model ↔ treating Π† as a coherent whole

## Decision-Determination in I/B/E Terms

**Definition from representation theorem:** The environment responds to policies, not to internal mechanisms.

**In I/B/E terms:** E's response depends on the external policy Π̈, not on D_B's internal structure.

**Formally:**
- Decision-determined: E = f(Π̈, D_E) for some f
- NOT decision-determined: E could depend on details of D_B beyond Π̈

**Example of non-decision-determined:**
- A predictor that can read the agent's source code
- The environment might discriminate based on *how* π is computed, not just *what* π is

**Example of decision-determined:**
- A predictor that can only observe the agent's behavior
- Environment responds to the policy (external behavior), not internals

## The Self-Trust Connection

**Paper's self-trust theorem:** In appropriate conditions, the agent doesn't prefer to self-modify.

**Representation theorem version:** A unified agent choosing an optimal policy has no reason to change its policy.

**The I/B/E connection:**

Self-modification = changing D_B (the boundary's decision rule)
Self-trust = D_B being stable (no preference to change it)

**Why unified agents have self-trust:**
1. The agent chooses policy π* maximizing E[U]
2. Self-modification would change π* to some π'
3. By optimality of π*, E[U | π*] ≥ E[U | π']
4. So no self-modification is preferred

**Condition needed:** The modification must be "fair" (decision-determined). If modification lets the agent achieve something π* couldn't (e.g., convince a source-code-reading predictor), this argument fails.

## The Paper's "Communicative Alternative" Condition

**The paper requires:** If modification opportunity exists, a communicative alternative should exist.

**Translation:** Any modification to D_B should be achievable by a policy choice in Π*.

**In representation theorem terms:** The policy space should include all relevant behavioral options. If "being a one-boxer" is achievable by modification, it should be achievable by policy choice.

**Why this matters:**
- Without this, modification might dominate policy choice
- The agent could prefer to self-modify, breaking self-trust
- The "fairness" (decision-determination) condition ensures policy choice is sufficient

## Instances as Applications of the Model

**Paper's definition:** "Instances" are the agent at different observations, factored by Ö (external observation).

**Reinterpretation:** Instances aren't ontologically separate. They're applications of the agency model to different contexts.

**The modeling story:**
1. We attribute agency to S (draw I/B/E boundaries)
2. We identify S's policy π: O → A
3. For each observation o, π(o) is what S does in that context
4. "Instance at o" = the application of the agency model where O = o

**Why this isn't UDT-biased:**
- Observation-based factoring is natural for any informationally-constrained agent
- The agent can't distinguish worlds with the same observation
- So the policy must be observation-level, not world-level
- This is a feature of limited information, not a UDT assumption

## The Representation Theorem as I/B/E Consequence

**Claim:** The representation theorem follows from taking I/B/E seriously.

**Argument:**
1. I/B/E decomposes the world into agent and environment
2. The boundary B implements a policy π: O → A
3. Unity means: there's one π, not separate optimizers for each o
4. Decision-determination means: E responds to π, not to B's internals
5. Rationality means: π is chosen to maximize E[U]
6. Conclusion: At each o, π(o) is part of the globally optimal policy
7. This is the UDT formula

**The theorem's content:** Steps 1-5 are what "coherent agency attribution" means. Step 6-7 are derivable consequences.

## Why the Paper's Framework is Compatible

The paper's formal structure is fully compatible with this interpretation:

| Paper's Framework | Representation Theorem Interpretation |
|-------------------|--------------------------------------|
| Defines I/B/E | Structural choice when attributing agency |
| Defines policies π | Agent's behavioral specification |
| Defines instances | Applications of the model |
| Proves self-trust | Consequence of unity + optimality |
| Communication | Enables coordination across instances |

**What the representation theorem adds:**
- Explicit argument that unity is the *default*
- Clearer connection to "what agency attribution means"
- Burden-of-proof argument against the split model
- Independent motivation for each axiom

## Remaining Work

1. **Formalize "unity" in I/B/E terms:** What does it mean mathematically for instances to be "the same agent"?

2. **Connect communication to functional identity:** How does the paper's communication structure relate to algorithmic identity across instances?

3. **Handle the semantic/side-channel distinction:** The paper distinguishes Ô (semantic) from Ǒ (side-channel). How does this affect the theorem?

4. **Address imperfect self-knowledge:** What if the agent doesn't know its own D_B?

## Summary

The I/B/E framework provides the mathematical structure for agency attribution. The representation theorem shows that:

1. Accepting I/B/E = accepting a single agent with a policy
2. Single agent + decision-determination + rationality = updateless reasoning
3. Updateless reasoning = self-trust (in fair problems)

The paper's results follow from taking the I/B/E decomposition seriously as a model of unified agency.
