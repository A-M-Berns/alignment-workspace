# Synthesis: Agency Attribution and Updateless Reasoning

## The Dissolution of "Instances"

The paper factors the agent by external observation, defining "instances" for each observation value. This is UDT-biased because it treats instances as primitive.

**Reframe:** "Instances" are not in the territory. They're applications of an agency model.

When I say "X is an agent with utility U," and I apply this model to X-at-time-1 and X-at-time-2, I have two "instances" - two contexts where I'm using the model.

The question "how should instances coordinate?" becomes: "if I apply the same model multiple times, what should I predict?"

**Answer:** The same model, applied with different inputs, gives different outputs. But it's the *same* model - specifically, the same policy pi: O -> A.

There's no mysterious coordination. There's just one model being applied consistently.

## Agency as Modeling

Drawing from "Meaning & Agency":

**Agency attribution** is a modeling choice. We choose to predict X's behavior using "X optimizes for U" rather than "X follows mechanism M."

This choice is appropriate when the teleological model (goals) predicts better than the mechanistic model (mechanism).

### What does the agency model look like?

The simplest agency model is:
- Inputs: observations O
- Outputs: actions A
- Rule: pi(o) = argmax_a E[U | pi(o) = a]

This model makes no reference to "time" or "instances." It's just: given observation o, output the action that would be part of the best policy.

### Where do "instances" come in?

When we apply this model to X existing in multiple contexts (times, locations, possible worlds), each application is an "instance."

But crucially, we're applying the SAME MODEL each time. We're not applying different models and asking how they coordinate.

## Three Arguments, One Conclusion

### Argument 1: Decision-Determination
In fair problems, the environment responds to policies, not mechanisms. So policies are the natural unit of analysis. Evaluating policies as wholes is updateless reasoning.

### Argument 2: Functional Identity
If instances run the same algorithm, their behavior is logically correlated. Correct conditioning accounts for this correlation. This requires conditioning on algorithmic properties, which is updateless reasoning.

### Argument 3: Parsimony
The simplest model of "single agent" is a single optimization. A single optimization across situations is updateless reasoning.

### The Common Thread
All three arguments lead to the same place: if you're modeling X as a *single* agent with utility U, the correct/simple/natural model is updateless.

The UDT formula pi(o) = argmax_a E[U | pi(o) = a] is what "single agent with utility U" means, formally.

## Toward a Formal Framework

### Definition: Agency Model
An **agency model** is a tuple (O, A, U, P, pi) where:
- O is the observation space
- A is the action space
- U: Omega -> R is a utility function on world-states
- P is a prior over Omega
- pi: O -> A is the policy

### Definition: Model Application
An **application** of an agency model at observation o is the prediction that action pi(o) will be taken.

### Definition: Model Correctness
An agency model is **correct** at observation o if the actual action equals pi(o).

### Definition: Model Coherence
An agency model (O, A, U, P, pi) is **coherent** if pi is optimal relative to (U, P):
for all o in O, for all a != pi(o), U'(pi) >= U'(pi[o -> a])

where U'(pi) = E_P[U | policy = pi] is the policy-level expected utility and pi[o -> a] is pi modified to output a at o. (This says: no single-observation modification of pi is strictly better. This is the modified-policy comparison matching the Lean formalization; the earlier draft wrote it as a conditional-probability comparison whose left side conditioned on the tautology pi(o) = pi(o), which was ill-formed. Fixed 2026-08-05.)

### Theorem (Informal)
If we model X as a single coherent agent with utility U and prior P, then X reasons updatelessly: for each observation o, X chooses the action that would be part of the globally optimal policy.

### What makes this a "representation theorem"?

We're showing: the meaning of "single coherent agent with utility U" is equivalent to "updateless reasoner with utility U."

The UDT decision formula is not just one option among many. It's what "agent with utility U" means when you take it seriously.

## The Interior/Boundary/Environment Framework

The I/B/E decomposition can now be understood as:

**Boundary (B):** The interface where the agency model is applied. Observations come in, actions go out.

**Interior (I):** Internal state that persists across applications. This enables communication between applications (instances).

**Environment (E):** Everything outside the boundary.

### How do these interact?

The agency model (pi) is applied at the boundary. Different observations at the boundary represent different applications.

The interior provides memory/communication between applications. This is how an instance at o1 can influence an instance at o2.

The environment responds to actions and generates observations. Decision-determination says: the environment only cares about the policy (the sequence of actions for each observation), not about the internal process.

### Where do "internal" vs "external" observations/actions come from?

**External observations/actions (Ö, Ä):** The interface with the environment.

**Internal observations/actions (Ȯ, Ȧ):** The interface with the interior (memory).

The full observation O = (Ȯ, Ö). The full action A = (Ȧ, Ä).

The policy pi: O -> A can be decomposed into:
- The external policy ¨pi: Ö -> Ä (what the environment sees)
- The internal policy ˙pi: O -> Ȧ (what gets stored in memory)

Decision-determination says: the environment responds to ¨pi, not to the full pi or to internal mechanisms.

## The Communication Layer

Communication between instances happens via the interior.

Instance at o1 performs internal action Ȧ1 (stores something in memory).
Instance at o2 receives internal observation Ȯ2 (reads from memory).

If Ȯ2 depends on Ȧ1, then o1 has communicated with o2.

### How does this relate to the updateless framework?

Without communication, each instance only has its local observation Ö. Instances with different Ö might fail to coordinate.

With communication, instances can share information. This enables coordination even when Ö differs.

### The paper's insight
Communication acts as a "release valve" for pressures toward self-modification. If you can achieve coordination by communicating, you don't need to modify your decision procedure.

## Putting It Together: The Representation Theorem Structure

**Axioms:**

1. **(Agency)** X is modeled as an agent: there exist O, A, U, P such that X's behavior is predicted by a policy pi: O -> A optimizing E_P[U].

2. **(Coherence)** The model is coherent: pi is optimal relative to (U, P).

3. **(Unity)** X is modeled as a *single* agent: there is one policy pi, applied at all observations.

4. **(Decision-Determination)** The environment responds only to the external policy ¨pi, not to internal mechanisms or the full pi.

**Theorem:** Under these axioms, pi satisfies the UDT formula:
pi(o) = argmax_a E_P[U | pi(o) = a]

**Interpretation:** The UDT formula is what "single coherent agent with utility U" means. It's not an additional assumption; it's a derivation from the meaning of agency.

## Open Questions

1. **The prior P:** Where does it come from? Is it part of the axioms, or derived from something?

2. **Ties:** What if multiple actions are tied for optimality? (The current treatment says argmax, but this is not unique.)

3. **Computational bounds:** Real agents can't compute E[U | pi(o) = a] exactly. How does the framework handle bounded rationality?

4. **Self-knowledge:** The functional identity argument required self-knowledge. Is this implicit in the other axioms, or does it need to be added?

5. **Reflective stability:** The original goal was a representation theorem connected to reflective stability. How does the current framework address self-modification?

6. **Imperfect unity:** What if instances are similar but not identical? How does the framework degrade gracefully?

## Next Steps

1. Formalize the axioms precisely
2. State and prove the theorem
3. Show that reflective stability follows (i.e., under these axioms, the agent doesn't prefer to self-modify)
4. Address the communication structure and how it enables coordination
5. Connect back to the examples in the paper (Coordinated Buttons, Third Button, etc.)
