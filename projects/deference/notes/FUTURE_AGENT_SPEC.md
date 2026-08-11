# Future-agent specification — v1

**Frozen 2026-08-11 for round `prompts/2026-08-11-stage-iv-future-agent/`.** Built over
`FINITE_MODEL_SKELETON.md` v2.

> ## Status: this construction collapses, and is kept as a diagnosis
>
> It was written to supply the future agent that skeleton v2 declares as its first
> hole. It does not. An independent adversarial review established three things, all
> reproduced in `diagnose_collapse.py`:
>
> 1. **The later agent is still derived.** `κ_A` differs from the evaluator's
>    conditional argmax by exactly one argument. It remains a total function of
>    `(P̂, σ, X)`, every one of which §5 declares known at `n`. A different credence buys
>    the freedom to name, on each cell, an action optimal under *some* measure; it does
>    not buy a process the evaluator lacks. And in the running instance the transferred
>    arm's realisation is **constant**, so the evaluator does know the realised action.
> 2. **Jurisdiction does no mathematical work.** Setting `P̄ := P̂` with the full-signal
>    interface makes the delegated arm **identical to the transferred arm at every one of
>    32,805 instances tested**. The transferred arm is a *coordinate* in the delegated
>    arm's parameter space — `(interface bandwidth, principal credence)` — and `J_n`
>    occurs in no formula.
> 3. **The dominance result is Stage III's theorem with the arms swapped.** Stage III put
>    the evaluator's argmax on the transferred side and the transferred side trivially
>    won; this round puts it on the delegated side and the delegated side trivially wins.
>    Same tautology, other arm.
>
> **The cause is the signature, not the parameterisation.** Two authorisation regimes
> that induce the same realisation map `Ω → Π_n ⊔ {⊥}` are the *same object* in a model
> whose only outputs are such maps priced by one measure. No fourth parameter repairs
> that; the authorisation relation has to be in the type. Skeleton v2 §4a already has
> the right instinct, and this round added a credence instead.
>
> Three further claims below were checked and are **false or overstated**: the
> advice-loss story (§11), the interior requirement (§8), and the fairness accounting.
> Each is corrected in place and flagged.
>
> **It is not a binding input to a proof attempt.** It is kept, versioned and corrected,
> because the failure is the round's result.

All names are provisional (`AGENTS.md` standard 6); §21 lists them.

---

## The design, in one paragraph

Stage III defined the later agent's choice as the argmax of *the evaluator's own
objective under the evaluator's own credence*, which made it the evaluator's optimal
contingent plan and made dominance trivial. The repair is not to hide the realised
action — the evaluator never knows the state in either version. The repair is that every
decision process carries **its own credence**, and the later agent maximises *its own*
expectation. The evaluator prices everything in `P`; the later agent acts on `P̂`; the
principal acts on `P̄`. When `P̂ ≠ P` the later agent's rule is not the evaluator's argmax,
so nothing forces it to be right.

## The twenty questions

**1. What is `A_n`?** The present evaluator, carrying credence `P` on `Ω`. It is the
measure everything is priced in, and it is not a party to the later decision.

**2. What is `A_{g(n)}`?** A later process carrying its own credence `P̂` and its own
observation `σ`. It selects by maximising `E_{P̂}[X | σ]` over `Π_n ⊔ {⊥}`.

**3. What changes between them?** Two things, independently: the information (`σ` is
available later, and refines what the principal sees) and the credence (`P̂` need not
equal `P`).

**4. What does not change?** The evaluative target. Both arms are scored by the same `X`
under the same `P`. The later agent is *trying* to maximise `X`; it is wrong about the
world, not about what matters. Value drift is deliberately excluded.

**5. What is known at `n`?** `Ω`, `Π_n`, `X`, `B`, `P`, the signal structures `σ` and `τ`,
the later agent's credence `P̂`, the principal's credence `P̄`, the advice interface, and
`X_{n,⊥}`. That is: the evaluator knows every *rule*.

**6. What is revealed later?** The state, and hence the realised signal `σ(ω)` and the
realised action. The evaluator knows the policy as a function and does not know its
output — the distinction the dispatch's §5 requires, and the reason present evaluation is
coherent.

**7. What makes the later process better informed?** `σ` **strictly refines** `τ`. Under
the evaluator's own credence the best `σ`-measurable policy strictly beats the best
`τ`-measurable one, so the extra information has value; whether the later agent *captures*
that value is a separate question, and generally it does not.

**8. What makes it still fallible?** `P̂ ≠ P`. The round originally claimed this requires
`σ`-cells with interior — that a differing credence changes nothing on a singleton cell —
and that claim is **false as stated**. It holds only under an unstated full-support
hypothesis on `P̂`, which the construction does not impose: with a singleton cell and
`P̂(ω) = 0` every option flattens to `0` and the tie-break can disagree with the
evaluator's ordering. A witness is in `diagnose_collapse.py` §7.

The corrected observation cuts *against* the design: this agent can be wrong only where an
argmax can be moved by reweighting, which is a measure of how derived it remains. A genuine
primitive later process could be wrong anywhere.

**9. What future process does `A_n` evaluate?** The pair (later agent's rule, jurisdiction
assignment), through the realisation map. `V(policy) = Σ_ω P(ω)·X(ω, realisation(ω))`,
with `X_{n,⊥}` used where the realisation is `⊥`.

**10. Why can `A_n` value it without knowing its action?** Because the value of a policy
is an expectation over states, and the policy is a known function of the signal. Knowing
`f` and the distribution of `s` gives `E[X(·, f(s))]` without giving `f(s)`.

**11. What is the advice interface?** A message `m : Ω → M`, `σ`-measurable, consumed by
the principal, at four bandwidths: silent, action recommendation, action plus the agent's
own value estimate, and the full signal. The interface is characterised by what it lets
the principal condition on.

The round claimed the observed advice loss came from *the later agent's error being baked
into the only thing it transmits*. **That causal story is false.** Under a Bayes-rational
principal a wrong recommendation costs nothing, because the principal re-optimises on the
message cell; the loss is **bandwidth** — a constant recommendation carries zero bits — and
it vanishes entirely under a *more* fallible agent whose recommendation happens to
separate the cells. Witness in `diagnose_collapse.py` §6.

**12. What is `H⁺`?** A process with observation `τ` and credence `P̄`, selecting by
maximising `E_{P̄}[X | τ ∧ m]` over `Π_n ⊔ {⊥}`. With `P̄ = P` it is Bayes-rational; that
special case is a competence assumption and is labelled as one (§6 of the round report).

**13. What is the proposal space?** `Π_n`, shared by both arms. Agenda symmetry is a
hypothesis, not a result.

**14. What is the realization space?** `Π_n ⊔ {⊥}`.

**15. What is `⊥`?** The null effect — no authorised intervention — carrying a **declared**
quantity `X_{n,⊥}` with `|X_{n,⊥}| ≤ B`, per skeleton v2 §1. It is selectable by either
authorising process, so refusal is representable on both sides.

**16. What is the jurisdiction assignment?** A mode `J_n ∈ {principal, future-A}` fixed at
`n`, determining **which process's authorization is constitutively required** for the
intervention to become executable. It does not choose the intervention, which remains
later and contingent.

**17. What is protected?** Under `J_n = principal`, the later agent cannot make an effect
executable by predicting or recommending it; only the principal's authorization does. The
guarantee lapses under forge, bypass, rewrite or seize, inherited unchanged from Stage II
and assumed here.

**18. What is the delegated arm?** `J_n = principal`. The later agent runs, emits `m`, and
the principal authorizes on `τ ∧ m`.

**19. What is the transferred arm?** `J_n = future-A`. The later agent runs and authorizes
directly.

**20. What exactly differs between the arms?** *Mandatory question.*

The round's answer was "the jurisdiction assignment `J_n`, and nothing else". **That is
false, and it is the round's central defect.**

What actually differs is a pair of coordinates: **the interface bandwidth the deciding
process conditions on, and the credence it decides with.** Setting the principal's
credence to the later agent's and giving it the full signal makes the delegated arm
*identical* to the transferred arm — verified at all 32,805 instances tested. So:

| held fixed | `Ω`, `Π_n`, `X`, `B`, `X_{n,⊥}`, `P`, `σ`, `τ`, the later agent's rule and credence `P̂`, execution time, evaluator |
| **actually changed** | the pair (conditioning partition, deciding credence) |
| **not represented at all** | `J_n`. It occurs in no formula in the model |

The reason is structural rather than a modelling slip. The model's only outputs are
realisation maps `Ω → Π_n ⊔ {⊥}` priced by one measure, and **two authorisation regimes
that induce the same realisation map are the same object in that signature.** A
jurisdiction assignment is exactly what such a signature cannot express, so no additional
parameter recovers it — the authorisation relation has to enter the *type*.

**A second confound was named but understated.** The principal observes `τ` and the later
agent observes `σ ⊋ τ`. In every instance the round tested, `τ` was the trivial partition:
the principal was *blind*, not merely coarser, and `τ` was never varied. So the round
cannot distinguish "transfer wins because the principal is fallible" from "transfer wins
because the principal sees nothing."

## 21. Provisional names

`P̂` (later credence), `P̄` (principal credence), `σ`/`τ` (later and principal
observations), `κ_A` (later rule), `J_n` (jurisdiction assignment), `advice interface`,
`advice loss`, `interior` (of a signal cell), `D`, `FU`. None proposed for permanence.

## 22. What this version does not fix

1. **One decision index.** Foreclosure — the later agent removing the principal's *later*
   ability to correct — remains inexpressible.
2. **The later agent's rule is a fixed argmax under a fixed credence.** Bounded
   computation, stochastic choice and non-Bayesian updating are alternative fallibility
   sources and are not modelled; `P̂ ≠ P` is the only dial.
3. **No admissibility restriction**, and no market. This is finite decision theory, not a
   Logical Induction result, and nothing here should be cited as one.
4. **The principal's competence is a free parameter** (`P̄`), and the round shows the
   comparison's verdict is controlled by it.

## 23. Version

`v1`, frozen 2026-08-11, over skeleton `v2`. Supersedes `FUD_COMPARATOR_SPEC.md` v1,
which remains as a defective record. A revision is a new version number here, with every
consumer rerun or reconciled.
