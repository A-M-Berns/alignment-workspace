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
| **P7** | genuine-learning control | **revised.** A *coherent* competing class passes clause (1) with `p_1 = 1/8`; clause (5) fails because the fixture cannot sustain a positive margin. No-information control exactly flat |
| **P8** | coverage failure | with the reason never raised, zero selected occasions and zero bad mass; the conditional rate raises rather than reporting a perfect score |
| **P9** | coverage algebra | `B_T/M_T` falls under dense exposure and is **constant** at the boundary `M_T = Theta(sqrt(T)) = Theta(B_T)`, so the condition is sharp |
| **P10** | replay optional | replay gap `5, 13, 29, 61` while the local bound holds at every horizon, on the same runs |

## 1. A claim withdrawn, and what replaces it

The first pass asserted that a *normatively coherent* repair class always leaves
its targets transient, so the construction always complies immediately. **That is
withdrawn.**

The inference was: a return route would have to say "there is an exposed burden,
so having acknowledged, stop acknowledging", which is not a repair. The error is
that a return route need not be licensed by the *same* reason. The `COMPETING`
class supplies one from a different certificate — `defeated_applicability`,
ordinary caution about not compounding an outstanding incoherence — and both
certificates hold in a single public state. There `hold` is recurrent, and every
edge stands on its own licence.

`INCOHERENT` and `COMPETING` produce the same graph, which is the decisive point:
**recurrence is no evidence of incoherence**, so the inference cannot be run.

What survives is the graph theorem alone:

```
b_g transient in the active repair graph  ->  p_t(b_g) = 0
```

Whether realistic grammars yield transient or recurrent targets is now an open
structural question about grammars.

The second, smaller limitation stands: with most actions absorbing the chain is
reducible, its stationary distribution is not unique, and the implementation
resolves the ambiguity from the initial uniform distribution. Mass redistributes
within a recurrent class and not between classes. That is this implementation's
solver, not Theorem 18.

## 1b. And the dynamics question is still undecided

With a coherent recurrent class the learner *does* start with mass on the target —
clause (1) of the pre-registered criterion, which the first pass said was
unreachable. But clause (5) fails: the mass rises rather than falls, because the
fixture's finite content set exhausts the supply of exposable contents and the
margin is positive on only 4–5 of 48 dates.

So the reason stops recurring *with a positive gap*, which is coverage failing
inside the fixture. **The dynamics question cannot be decided here**, and the
requirement is a regenerating fixture rather than a different learner. The
no-information control remains exactly flat, so what movement occurs is
feedback-driven.

## 1c. Modularity of bounds is not modularity of dynamics

Adding an otherwise lawful competing repair leaves every per-repair inequality
untouched — each reads only its own map — and changes which responses the learner
can put mass on at all. A grammar therefore cannot be validated repair by repair.

## 2. The two load-bearing hypotheses are not proved

`H4` (a *certified* repair class) and `H6` (coverage). Neither is a regret
question. After the refinement they are no longer symmetric: H6 is a legitimate
hypothesis with a plausible external supplier, while H4's word `certified` is the
one thing that must be given content before the abstract theorem means what it
says — `COMPILER_SOUNDNESS.md`.

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
