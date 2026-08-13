# Prosecution

The ten prosecutions, then the three places the crown jewel is weaker than it
reads.

| | prosecution | outcome |
|---|---|---|
| **P1** | the denominator matters | `M_T` is `T` under the dense schedule and exactly `4, 8, 16, 32` at `T = 16, 64, 256, 1024` under the sparse one. Under sparse, a learner mishandling *every* selected occasion still has `Q_T/T -> 0`. The unconditional rate certifies nothing |
| **P2** | multiple repairs simultaneously | several selected on the same dates; each keeps its own inequality; recomputing each independently reproduces it exactly, so the bounds do not interfere |
| **P3** | conflicting lawful repairs | `hold` is the source of two repairs with different replacements. Nothing breaks — the lemma is per repair. Conflict shows up as two exits in the rule graph and is a compiler question |
| **P4** | lawful with no positive margin | a certified repair with margin `-2`. `bad_mass_bound` raises rather than returning a number, so no learning conclusion is available for it |
| **P5** | margin derived | the acknowledge schema's side condition is a public predicate; where it holds the observed margin is `1/2`, equal to the certificate's weight. Where it fails, `None` is returned rather than a zero claimed |
| **P6** | transience characterisation | one-way class: `{hold, disavow}` get zero mass. Add a return edge: only `{disavow}`. A 3-cycle: none. The condition is exactly the absence of a return route, and the identity self-loop does not rescue it |
| **P7** | genuine-learning control | the coherent class **fails clause (1)** — no initial mass to shed. The cyclic class passes, including the no-information control. See below |
| **P8** | coverage failure | with the reason never raised, zero selected occasions and zero bad mass; the conditional rate raises rather than reporting a perfect score |
| **P9** | coverage algebra | `B_T/M_T` falls under dense exposure and is **constant** at the boundary `M_T = Theta(sqrt(T)) = Theta(B_T)`, so the condition is sharp |
| **P10** | replay optional | replay gap `5, 13, 29, 61` while the local bound holds at every horizon, on the same runs |

## 1. The construction complies rather than learns

The central weakness, and it is structural rather than a fixture accident.

For any repair class whose rules point away from mistakes with no return route
active at the same date, the targeted response is transient in the rule-mixture
chain at exactly the dates the repair fires. The stationary distribution gives it
zero mass. `Q_T(g) = 0` identically, and the crown jewel is satisfied without the
learner ever making the mistake.

A return route active at a selected date would have to say "there is an exposed
burden, so having acknowledged, stop acknowledging". That is not a repair. So the
better the repair grammar, the more completely the construction complies
immediately.

What the round *can* show is that the engine is not merely hard-coded: on a class
where the target is recurrent, the within-class share moves with feedback, freezes
exactly when the margin goes to zero, and does not move at all when the loss is
replaced by an uninformative one. Feedback-responsiveness is real; a coherent
repair class removes the occasion for it.

There is a second, smaller limitation visible in the same run: with most actions
absorbing the chain is reducible, its stationary distribution is not unique, and
the implementation resolves the ambiguity from the initial uniform distribution.
Mass redistributes within a recurrent class and never between classes. That is a
property of this implementation, not of Theorem 18, and it caps how much movement
any fixture of this shape could display.

## 2. The two load-bearing hypotheses are not proved

`H4` (a repair class) and `H6` (coverage). Everything mathematical is downstream of
them and neither is a regret question.

Coverage is the more serious. The theorem is conditional on being asked, and a
reasoner that arranges to be asked nothing satisfies it vacuously — P8 displays
exactly that. The corrigibility composition is the natural place to close it and
is stated as a target, not a theorem: the merged deference result gives a
capability that survives every advisor policy, and what coverage needs is an
*exercise rate*, which no arc currently supplies.

## 3. Margin derivation covers a schema, not the class

`P5` derives the margin for the acknowledge schema under a public side condition.
It does not derive margins for the other repairs, and one of them has a negative
margin. So H5 is discharged for one schema and remains a hypothesis for the class.

## What was not attacked

- Whether the `O(sqrt(T |A| log K))` bound is *attained* on this process. Only the
  lemma's inequality was checked; regret was never measured against the bound.
- Any complexity model for a generated grammar. `log K` is where it would enter.
- Whether a no-regret learner exists whose distribution is not a fixed point of
  the rule mixture. Named as the open dynamics question, not investigated.
- Vocabulary migration and what a selector refers to across it.
- Multi-scorekeeper aggregation: the loss still reads a single critic.
