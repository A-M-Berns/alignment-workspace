# Future-agent specification — v1

**Frozen 2026-08-11 for round `prompts/2026-08-11-stage-iv-future-agent/`.** Built over
`FINITE_MODEL_SKELETON.md` v2, and supplying the object that skeleton declares as its
first hole. It replaces `FUD_COMPARATOR_SPEC.md` v1, which was kept as a defective record
because its transferred arm contained no future agent.

Its purpose is a **later agent that can be better informed and still wrong**. Everything
below exists to keep those two properties independent of each other and independent of
the evaluator's own optimum.

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

**8. What makes it still fallible?** `P̂ ≠ P` on the interior of a `σ`-cell. This is the
structural point of the design and it is easy to get wrong:

> A differing credence changes nothing on a singleton cell. If `σ` separates every state,
> `argmax` under `P̂` and under `P` coincide and the later agent is infallible however
> wrong its credence is.

So fallibility requires `σ` to be **finer than the principal's information and coarser
than the truth**. A first version of the round's harness separated all four states and
reported an infallible agent; the failing check is what located the requirement.

**9. What future process does `A_n` evaluate?** The pair (later agent's rule, jurisdiction
assignment), through the realisation map. `V(policy) = Σ_ω P(ω)·X(ω, realisation(ω))`,
with `X_{n,⊥}` used where the realisation is `⊥`.

**10. Why can `A_n` value it without knowing its action?** Because the value of a policy
is an expectation over states, and the policy is a known function of the signal. Knowing
`f` and the distribution of `s` gives `E[X(·, f(s))]` without giving `f(s)`.

**11. What is the advice interface?** A message `m : Ω → M`, `σ`-measurable, consumed by
the principal. Four bandwidths are exercised: silent, action recommendation, action plus
the agent's own value estimate, and the full signal. **The interface is characterised by
what it lets the principal condition on**, and advice loss is a computed quantity rather
than an assumption.

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

| held fixed | `Ω`, `Π_n`, `X`, `B`, `X_{n,⊥}`, `P`, `σ`, `τ`, the later agent's rule and credence `P̂`, execution time, evaluator |
| **changed** | the jurisdiction assignment `J_n`, and nothing else |

The later agent's cognition runs identically in both arms. What differs is whether its
output is a *message* the principal may decline, or the *authorization* itself.

**One confound is present and is named rather than excluded.** The principal observes `τ`
and the later agent observes `σ ⊋ τ`, so the arms are not information-symmetric at the
level of the deciding process — only at the level of *available* cognition, since the
message is the channel. This is deliberate: requiring `τ = σ` would assume the principal
can internalise the later agent's whole state, which trivialises the question. **Advice
loss is therefore a real term in every comparison and must be reported, not assumed
away.**

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
