# Objections and Responses

## Objection 1: "You've just defined UDT as correct"

**Objection:** The representation theorem defines a class of agents (those satisfying the axioms) and shows they reason updatelessly. But this is just defining UDT agents and showing they reason like UDT. What's the contribution?

**Response:** The contribution is in the *axioms*, not the theorem.

The axioms are supposed to capture "single coherent agent" - a natural concept that decision theorists (should) already care about. The theorem shows this natural concept implies UDT.

If someone accepts the axioms but rejects UDT, they're confused. If someone rejects the axioms, they're rejecting the concept of "single coherent agent" - which is a substantive position they should defend.

The theorem doesn't define UDT into existence. It shows UDT is the unique decision theory for agents satisfying independently-motivated axioms.

## Objection 2: "CDT agents are a different class"

**Objection:** Maybe CDT agents satisfy different axioms. You've shown UDT is correct for UDT-like agents, but CDT is correct for CDT-like agents.

**Response:** The question is which axioms capture "good reasoning."

The axioms I've proposed capture:
- Modeling oneself as an algorithm (functional identity)
- Being a single agent across situations (unity)
- Facing problems where only behavior matters (decision-determination)

These are natural properties for an agent to have. An agent that lacks them has something wrong.

A CDT agent fails unity: it treats each instance as a separate optimizer. But this is incoherent with claiming to be "one agent."

If you want to defend CDT, you need to either:
(a) Reject unity - but then you're not modeling "one agent"
(b) Accept unity but reject its implications - but the implications follow logically

## Objection 3: "Self-knowledge is too strong"

**Objection:** Real agents don't know their own algorithms. The axiom of self-knowledge is unrealistic.

**Response:** This is a real limitation. The theorem is about idealized agents with perfect self-knowledge.

For realistic agents, we'd need to handle **uncertainty about one's own algorithm**. This is the "logical uncertainty" problem, which is a deep open question.

However:
1. The idealized case is still informative. It tells us what correct reasoning looks like when self-knowledge is possible.
2. Approximate self-knowledge might lead to approximate UDT reasoning.
3. Some practical settings (e.g., AI systems inspecting their own code) approximate self-knowledge.

The theorem is a limit case; realistic agents approximate it.

## Objection 4: "Decision-determination is too restrictive"

**Objection:** Real problems aren't decision-determined. The environment often cares about more than just behavior.

**Response:** Decision-determination is a **fairness** condition. It defines which problems are appropriate for evaluating decision theories.

In unfair problems, any decision theory can be made to look bad. (E.g., "become an alphabetizer or I destroy the world.")

The claim is: in fair problems, UDT is correct. If you're facing unfair problems, good luck - no decision theory can help.

This is analogous to VNM: the theorem assumes certain structural properties (coherent preferences). If those fail, EU maximization doesn't apply. That doesn't make the theorem useless.

## Objection 5: "The theorem is circular"

**Objection:** You assume the agent maximizes expected utility, then derive it maximizes expected utility (with UDT conditioning). This is circular.

**Response:** The contribution is justifying the **conditioning**, not EU maximization.

Everyone agrees: maximize E[U | something]. The question is what "something" is.

- CDT: something = do(A=a), causal intervention
- EDT: something = A=a, evidential updating
- UDT: something = F(o)=a, algorithmic fact

The axioms justify UDT conditioning. They don't justify EU maximization (that's assumed).

If you want to go deeper, you'd need axioms that derive EU maximization itself. That's possible (VNM theorem) but orthogonal to the current contribution.

## Objection 6: "Instances don't exist"

**Objection:** The framework assumes there are "instances" of the agent. But maybe there's just one instance - me, right now.

**Response:** The framework doesn't assume instances exist in the world. It says: if you model yourself as an algorithm, and that algorithm might apply in multiple situations, then those situations are "instances."

If you think the algorithm only applies once, then there's only one instance. UDT and CDT agree in single-instance cases.

The interesting cases are when you acknowledge multiple instances (copies, future selves, counterfactual selves). Then UDT says: reason as if choosing for all of them.

## Objection 7: "Algorithms don't choose"

**Objection:** You say the agent "is" an algorithm F. But algorithms just execute; they don't choose. So what does it mean for the agent to "choose" action a?

**Response:** This is the self-reference puzzle.

The agent implements F. F is defined by how the agent reasons. The agent reasons using facts about F. This is circular, but not viciously so.

Think of it like this: the agent has beliefs about what algorithm it implements. It uses those beliefs to compute E[U | F(o)=a]. The action it takes determines what algorithm it actually implements. If its beliefs are correct, everything is consistent.

The "choice" is the computation of argmax. The algorithm F just is this computation. The agent doesn't choose F; the agent is F.

## Objection 8: "This doesn't help with Newcomb"

**Objection:** In Newcomb's problem, the predictor predicts before you decide. How does reasoning about your algorithm help?

**Response:** The predictor predicts your **algorithm**. If you're a one-boxer algorithm, you get predicted to one-box. If you're a two-boxer algorithm, you get predicted to two-box.

UDT says: "I am algorithm F. If F one-boxes, the predictor predicted one-boxing, so I get $1M. If F two-boxes, the predictor predicted two-boxing, so I get $1K."

E[U | F(o) = one-box] = $1M
E[U | F(o) = two-box] = $1K

So UDT one-boxes. This is the "correct" answer (you get more money).

CDT fails because it imagines a surgical intervention that doesn't change what the predictor predicted. But the predictor predicted based on your algorithm - you can't change your action without changing your algorithm.

## Objection 9: "What if the environment knows more than the policy?"

**Objection:** Decision-determination says the environment only responds to the policy. But what if the environment can see internal computation?

**Response:** Then decision-determination fails, and the theorem doesn't apply.

However: if the environment sees internal computation but can't distinguish algorithms with the same policy, then decision-determination still holds in a weaker sense.

More generally, the theorem applies when utility is a function of (policy, environment), not of (internal state, environment).

## Objection 10: "This is just causation with more steps"

**Objection:** You say "my algorithm causes my action, my action causes outcomes." Isn't this just CDT with a different causal model?

**Response:** Sort of, but the causal model is different in an important way.

CDT's causal model: action directly causes outcomes. You can intervene on action without changing anything upstream.

UDT's causal model: algorithm causes action, action (as part of policy) causes outcomes. You can't intervene on action without intervening on algorithm.

The difference is whether action is a "free variable" (CDT) or is determined by the algorithm (UDT).

If you model yourself as an algorithm, the UDT causal model is correct. If you model yourself as a free-floating choice, the CDT causal model might seem right (but it's incoherent).

---

## Summary of Key Points

1. **The axioms are the contribution.** They capture "single coherent agent" independently of UDT.

2. **CDT fails the axioms.** Specifically, it fails unity (treats instances as separate) or incorrectly reasons about the implications of unity.

3. **Self-knowledge is idealized** but informative. It defines correct reasoning when possible.

4. **Decision-determination is a fairness condition.** It defines which problems are appropriate for evaluating decision theories.

5. **The theorem is not circular.** It justifies the conditioning, not EU maximization.

6. **Instances are model-relative.** They're applications of the agency model, not things in the world.

7. **Algorithms can "choose"** in the sense that their output is determined by their structure, which includes reasoning about that structure.
