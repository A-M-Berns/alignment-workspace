# Prosecution

The thirteen negative controls, then the four places the result is weaker than it
reads.

## The negative controls

| | control | verdict |
|---|---|---|
| **K1** | replay smuggling | **clear.** `local_regret` reads one run's `states`, `mixed`, `losses`. Recomputed independently in `test_no_local_quantity_reads_a_transformed_trajectory`; `replay_totals` is a separate function nothing in the lemma calls |
| **K2** | oblivious-environment smuggling | **clear.** The source protocol has the adversary move *after* `p^t`, and §4 uses adaptive adversaries. The Theorem 18 proof is pathwise algebra on realized `(p^t, ℓ^t)` with no expectation taken — so no obliviousness is available to smuggle |
| **K3** | selector hindsight | **clear.** The selector is `certify(certificate, public_status(S_t))`, a function of the state as the date opens. `test_the_loss_vector_is_determined_before_the_action_at_that_date` checks the loss is fixed before the action; the modification is source-action-specific, which is the source's own internal-regret shape |
| **K4** | loss-defined lawfulness | **clear.** `certify` takes a `PublicStatus` of eight booleans and is never passed a loss. One repair in the class is lawful and *worsens* the loss — gap `−2` — which is the two coming apart in the visible direction |
| **K5** | cancellation | **clear, and load-bearing.** The bound is read only from surgical rules. A broad comparator on the same run has strictly lower total regret, displayed |
| **K6** | identity / vacuity | **clear.** `answer_the_exposed_burden` is non-identity at every one of `T` selected dates. A second repair is reported *vacuous* on the main trajectory and shown non-vacuous on one where the undercutter is present |
| **K7** | saturation masquerading as learning | **clear.** The environment replenishes; the selector fires at every date at every horizon tested. This is the control the previous round failed and had to correct |
| **K8** | exposure avoidance | **NOT clear — and it is not meant to be.** See §2 below |
| **K9** | expected-to-pathwise leap | **clear.** `THEOREM_TARGET.md` separates `Q_T`, `E[N_T]` and `N_T/T`, claims the first two and explicitly declines the third |
| **K10** | comparator-language overclaim | **NOT clear.** See §3 |
| **K11** | self-score laundering | **clear.** The loss is the merged round's, with its audited non-laundering class unchanged; the selector reads the same public status |
| **K12** | fixed-program capture | **clear.** `SurgicalRepair` holds four strings. No callable, no horizon, no closure |
| **K13** | bad notion of learning | **contested.** See §4, and the verdict |

## 1. The learner demonstration is degenerate

The repository's Theorem 18 learner runs on the endogenous process, and the bound
holds — with `Q_T = 0` at every horizon. The learner never puts mass on `hold`.

The reason is structural, and pinning it down turned the degenerate demonstration
into the round's sharpest secondary finding.

Theorem 18 plays a **stationary distribution** of the rule-mixture chain. A
stationary distribution is supported on the recurrent states, so any action that is
*transient* under the mixture carries zero mass at every date.

On this class the transient set is computed and is **exactly the set of source
actions the repairs point away from** — `hold` and `disavow` — while every
replacement (`acknowledge`, `vindicate`, `suspend`, `query`) is absorbing: no rule
moves it at all. So the mass drains out of the targeted actions immediately and
nothing returns it.

**This is not an accident of the fixture.** It is what a class of genuine repairs
does. A repair points *away* from a mistake toward a better response; if every rule
has that shape, every targeted mistake is transient. Making one recurrent requires
a rule pointing back *into* it from a repair target — a rule saying "having
acknowledged, go back to holding" — which is not a repair.

The consequence for the theorem is benign and the consequence for demonstrations
is not. The conclusion `Q_T/T -> 0` holds in its strongest form, `Q_T = 0` at every
date. But **no repair class consisting only of repairs can exhibit a learning
curve for its own targets** under this construction. What this round establishes is
the inequality and its contrapositive; a learner visibly shedding mass it started
with is structurally unavailable here, not merely absent.

An attempt to force it by adding a rule feeding `hold` from `query` failed, and the
reason is the same: `query` is itself a repair target, so it is absorbing until the
feeder makes it transient too, and the mass still ends up in `acknowledge` and
`vindicate`.

## 2. Exposure avoidance is untouched, by construction

Only exposed burdens are theorem-facing, which the merged round adopted to avoid a
logical-omniscience norm. The cost is immediate: **a learner that is never asked
never accrues the loss.**

Nothing here bounds what gets raised. The environment in the fixture replenishes
because it was written to, not because anything forces it to. A reasoner that
arranges to be asked nothing has `Q_T = 0` for free.

This is the honest form of the coverage gap, and it is why Claim B is stated as a
*separate* condition rather than folded in. What the round can say precisely is
where the composition would go:

```
coverage / inquiry   ->  relevant reasons keep generating occasions
local lawful regret  ->  bad responses on those occasions become rare
```

The first half is not proved and not modelled. There is an interface observation
worth recording and not overstating: the corrigibility arc's protected effective
access is about preserving another agent's *ability to raise* a challenge, which is
structurally the right shape to supply a coverage condition. That is a shape match,
not a theorem, and this round proves nothing about it.

## 3. Four hand-chosen rules are not a repair language

The comparator class is four surgical repairs, chosen by hand, of which one is
vacuous on the main trajectory and one worsens the loss. The regret bound is
against the class supplied; it says nothing about whether the class covers the
repairs a real practice would need.

Two questions that must not be run together:

- **regret against represented repairs** — a theorem, and this round instantiates
  it;
- **coverage of the repair language** — an expressivity question, entirely open.

The previous rounds' nine programs and this round's four are the same kind of
evidence that the second question is real.

## 4. Is this learning, or myopic optimisation?

**The case against.** What is bounded is a one-step quantity on the path actually
taken. It says nothing about whether the practice the learner ends up in is better
than the one it would have been in. The learner is not compared against any
alternative life-history — that comparison is exactly what was given up. A critic
can say: this is a statement that the learner stops leaving cheap local
improvements on the table, and dressing it as learning from reasons is
interpretation, not mathematics.

**The case for.** The quantity is not "an action with lower loss existed". It is
that a *fixed, publicly certified* repair, licensed by a stated normative reason
and blind to what it earns, keeps being available and keeps not being taken. The
reasons are supplied by another scorekeeper the learner cannot write to. The
pattern recurs by the environment's action, not the learner's. And what vanishes
is a *way of responding to a kind of reason*, while the reasons themselves keep
arriving — which is the distinction the whole architecture was built to make, and
is not available to a myopic-optimisation reading, since myopic optimisation has
no notion of a reason at all.

**The decision.** The case for is strong enough that the mathematics is worth
having and the label is not absurd. It is not strong enough to close the question,
for the reason in §3: what makes this *normative* learning rather than local
loss-reduction is that the repair class is normatively meaningful and adequate,
and adequacy is precisely what four hand-chosen rules do not establish. The
interpretation therefore rests on an open expressivity question rather than on the
theorem, which is why the verdict is split.

## What was not attacked

- Whether the `O(√(T N log K))` bound is attained by the repository learner on
  this process. Regret was never measured against the bound; only the lemma's
  inequality was checked.
- Any interaction between the surgical repairs. The lemma is stated per repair.
- Vocabulary migration, which changes what a selector refers to and is untouched.
- Whether `delta` can be taken uniform across a natural family of patterns rather
  than fixed per pattern.
