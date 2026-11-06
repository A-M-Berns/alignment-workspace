# Value change as belief change

**Status: a thesis under examination, with a machine-checked finite core.** The
transform and its worked consequences live in the note
[value-change-as-epistemic-update](https://github.com/A-M-Berns/alignment-workspace/blob/774eb891ac8e7222a6030ac345e6e8b90c91eced/projects/deference/corrigibility-note-dump-2026-10-01/value-change-as-epistemic-update.md)
(2026-09-29, revised through 2026-10-07); its finite claims were checked in Lean 4 as the
clean-room package
[corr-value-change](https://github.com/A-M-Berns/alignment-workspace/blob/774eb891ac8e7222a6030ac345e6e8b90c91eced/projects/deference/faf-cleanroom-2026-10-07-corr-value-change/README.md)
(1,361 declarations, gate PASS, four audit rounds), and the worked example's numbers are
asserted exactly by the note dump's fixtures. Nothing from it is registered; the
thesis-level reading is open. This is one move inside the corrigibility landscape — the
base of the `value-change-base-layer` programme — beside routes, such as the response-authority
kernel, that do not rest on it.

## The problem it addresses

The standard argument for corrigibility's anti-naturality: an expected-utility maximizer
evaluates everything, including proposals to change it, by its current utility function,
and no alternative function selects an act better by the current one's standards. So a
rational agent resists value change unless paid — Omohundro's goal-content integrity, the
Gandhi murder-pill.

The note's reply begins with an observation the argument skips: a value swap is an event
in the world. An embodied agent's utility change is a physical reconfiguration, and once
the swap is represented as an event, the value of changing decomposes into three terms:
the never-positive term the simple argument sees, a payment term (intrinsic preference
about the change or the world's response to it), and an information term — the value of
what the change's outcome reveals about facts the agent already cares about.

## The thesis

The information route is the puzzling one, and the transform explains it. Write the
agent's values as a random variable on an expanded algebra; the utility function it acts
on is the conditional expectation of that variable given what it knows — a
*representation* of its values, not the values themselves. A trusted change then improves
the representation in two precise senses: closer to the value variable in mean square,
and better at selecting acts (the note's Theorem 2.4). The simple argument's hidden
assumption is that the modification event carries no information about what is valuable —
a fact about which utility function the agent has, not about expected-utility
maximization.

The position statement's own framing is deliberately non-realist: the move is "just a
transformation in how we represent the agent"
([position-statement](https://github.com/A-M-Berns/alignment-workspace/blob/774eb891ac8e7222a6030ac345e6e8b90c91eced/projects/deference/corrigibility-note-dump-2026-10-01/position-statement.md)
§2.2). The same rational transition is a genuine change of utility function on the coarse
algebra and conditioning with the utility held fixed on any algebra containing the
modification event (§3 of the note).

## What is established, and what is not

Established at machine-checked strength, unregistered: the three-term decomposition, the
transform and Theorem 2.4, reflection conditional on legitimacy (a change is learning on
legitimate worlds and a priced residual pill on the rest, §2.6), value-by-value trust
where the agent's language cannot name whole states (§2.7), and two subsidiary findings —
no-expected-net-update is necessary but not sufficient for a change to be worth wanting,
and a utility change with beliefs held fixed reproduces a rational belief change on the
immediate decision only.

Open: whether the representation carries to systems corrected through training, which is
the `value-change-base-layer` programme's question; the choice of decomposition is not
unique, and which refinement (a modest-source trust relation is one filed route) survives
contact with a trained system is not settled. The note's §7 lists its own open questions.

## Where it sits

If the thesis holds in the trained-system setting, the anti-naturality obstacle is
reframed for agents whose corrections are information: corrigibility stops being a fight
against instrumental convergence and becomes a question about trust in the correction
channel — which is where [legitimacy](Legitimacy) and the deference corpus's trust
relations take over. The criterion is formalism-relative by the author's ruling: Total
Trust in the decision-theoretic setting, equivalent to reflection in the
logical-induction setting
([position-statement-v2 §1.5](https://github.com/A-M-Berns/alignment-workspace/blob/2a00dafc6c898c52b4c44bf54a41393026cdeb14/projects/deference/corrigibility-note-dump-2026-10-01/position-statement-v2.md)).

The transform also locates fully updated deference exactly: the information term
vanishes as the agent comes to know what its correctors know, and under reflection a
predicted correction is already adopted — the residual, corrections predicted and not
adopted, are precisely the ones the agent judges illegitimate (the note's §7(iii)).
What persists once nothing is left to learn is the payment term: a fact about which
utility the agent has, not a consequence of its rationality (§1.5). If the thesis does
not carry to trained systems, the kernel route through response authority stands
independently.
