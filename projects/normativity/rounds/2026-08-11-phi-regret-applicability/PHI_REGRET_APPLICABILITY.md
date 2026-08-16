# Φ-regret applicability

## Verdict

**Near miss.** Blum and Mansour's Theorem 18 is the right source theorem for the
frozen configuration, and causal guarded programs fit its history-dependent
modification rules. The current repository encoding does not meet the theorem's
fixed-action-set hypothesis: repository `Response` values contain
occasion-specific ledger effects, so their union through horizon `T` has
`N_T=3T+5`, not eight actions. The resulting theorem bound is linear in `T`.

Two repairs remain: a fixed eight-label action type with a proved
occasion-local encode/decode bridge, and an enforced or finitely audited
non-capturing rule interface. Until those land, item 30 is not ready. The
unrestricted replay substrate is farther outside the theorem: solvency coupling,
endogenous filings, replay-prefix guards, or post-hoc affordability filtering
would each leave its additive fixed-comparator setting.

If the missing fixed-`N` bridge is supplied, the applicable source bound is

```
R_T(F) = O(ell_max * sqrt(T * N * log K))
```

for every one of `K` fixed modification-rule programs on a fixed action set
of size `N`, with one time selector. The source's theorem states the bound with
`N log(MK)` under the square root; here `M = 1`. It does not give
`O(ell_max sqrt(T log K))`. No regret bound has been proved or measured for a
workspace learner.

## The exact online object

At round `t`, let `x_t` contain the occasion, bound schedule, reasons,
obligations, and responses strictly before `t`. Let `A_t` be the nonempty finite
set of available responses and `a_t in A_t` the learner's response. The loss is

```
ell_t(a) = charge_of(occasion_t, a) in [0, ell_max].
```

A lawful comparator is a fixed program

```
phi : (x_t, a in A_t) -> (b, grounds, authority) or no-proposal
```

whose date-`t` transformation is

```
F^t_phi(x_t)(a) = b  if guard_phi(x_t,a) and Check_t(x_t,a,b,...) = admitted
                   a  otherwise.
```

Thus the comparator's exact type is a **fixed ex-ante, causal, guarded
history-indexed modification-rule program** inducing a family
`F^t_phi(x_t): A_t -> A_t`. It is not one time-independent action map. Guard and
certificate failure are identity branches, so partiality is totalized without
changing loss. The class is a finite declared set of programs.

Historical lawfulness is evaluated from the actual pre-action state. The
program may inspect reasons filed by `t`, but cannot inspect the date-`t`
transcript response except through its candidate-action argument and cannot
inspect charges or accounts. This round's `PreActionReader` supplies the missing
strict-prefix boundary, and `sealed_legality_state` removes future records,
account labels, service costs, and actual tariffs before arbitrary rule and
policy code runs. The preparation reader uses `<= t` for responses, retains the
whole history internally, and passes an occasion carrying its tariffs. Omitting
a virtual `charges` table therefore did not by itself enforce either causality or
profit independence. It is a replay reader, not an online legality boundary.

## Comparator intervention and loss

The item-30 configuration has actual-prefix guards, frozen arrivals, and
`Accounting({}, suspends=False)`. Its intervention is a sequence of local
substitutions followed by return to the actual transcript at unfired occasions.
Consequently

```
L_T(H^phi) = sum_t ell_t(F^t_phi(x_t)(a_t)).
```

The executable adapter reproduces preparation replay on the canonical one-shot
repair. With suspension enabled, a firing can change later service and the
equality fails; `E10` and `E10b` already witness `Theta(T)` lifetime influence.
No-solvency-coupling is therefore the condition that converts replay charge into
the additive loss used by the reduction. Fencing alone does not.

The charge vector is full information: for every response in `A_t`, its charge
is computed from the frozen schedule. It is bounded by the schedule's service
window. This is low **charge** regret only; it is not a result about moral truth
or normative correctness.

## Primary-source theorem

The source audited is Avrim Blum and Yishay Mansour, “From External to Internal
Regret,” JMLR 8 (2007), §§2, 3, 6, 7, especially Theorem 18
([article page](https://www.jmlr.org/beta/papers/v8/blum07a.html),
[PDF](https://www.jmlr.org/papers/volume8/blum07a/blum07a.pdf)).

Their model has a fixed finite action set `{1,...,N}`. At each round the learner
chooses a distribution `p^t`, then receives a loss vector in `[0,1]^N` and incurs
its expectation. A modification rule takes history and an action and returns an
action; the paper writes `F^t` for its history-indexed date-`t` map. Theorem 18
allows a finite set of `K` such rules and `M` time-selection functions. It keeps
one weight for each `(source action, selector, rule)`, mixes rules separately in
each source-action row, and chooses `p^t` as a stationary distribution of the
resulting stochastic matrix. The full loss vector updates all weights. Its proof
is pathwise algebra for bounded loss vectors; the workspace's exogenous loss is
a stronger environment restriction.

Theorem 5 is the fixed swap-map special case and uses `N` external-regret
learners, one per source action. It is insufficient for these prefix guards.
Theorem 18 is the history-dependent extension that fits after compilation.

Gordon, Greenwald, and Marks, “No-Regret Learning in Convex Games,” ICML 2008,
Theorem 1 ([PDF](https://www.cs.cmu.edu/~ggordon/gordon-greenwald-marks-icml-phi-regret.pdf)),
instead assumes a fixed convex compact action region and a fixed convex compact
set of transformations `phi:A->A` with fixed-point and external-regret
subroutines. It does not directly license prefix-indexed guards. The preparation
round conflated that general Φ language with Blum--Mansour's history-dependent
modification-rule theorem.

## Hypothesis mapping

| theorem requirement | workspace classification | reason |
|---|---|---|
| finite fixed action set | false in the current encoding | semantic choices number eight, but repository `Response` equality carries occasion IDs and yields `N_T=3T+5` |
| nonempty availability | satisfied directly | every schedule has default and decline responses |
| finite rule class `K` | satisfied directly as a specification | item 30 declares nine programs; two remain to be materialized before running it |
| rule fixed ex ante | requires a lemma/audit | the program can be fixed while behavior varies, but two rules are absent and callbacks can capture external state |
| history-dependent rule allowed | satisfied directly | BM §2 defines rules on history and action; Theorem 18 uses `F^t` |
| rule closes on the action set | requires a lemma | current maps close locally; the missing fixed-label decoder must preserve closure |
| guard known before current loss | satisfied after harmless encoding | `PreActionReader` removes the date-`t` transcript response; reasons and schedule are already live |
| loss vector in `[0,1]^N` | satisfied by scaling | divide exact charges in `[0,ell_max]` by `ell_max` |
| additive per-round loss | satisfied only in frozen v1 | no suspension, frozen filings, actual-prefix guards |
| full-information feedback | satisfied directly | every action charge is exactly computable from the bound schedule |
| adversarial loss sequence | satisfied directly | BM permits arbitrary bounded vectors; the frozen schedule is exogenous |
| one selector or finite selectors | satisfied directly | use the always-one selector, `M=1` |
| stationary distribution computable | satisfied directly for each finite matrix | a finite stochastic matrix has one; this does not cure horizon-growing dimension |
| no post-hoc comparator deletion | satisfied only in item 30 | one occasion per date and work cap 3 make every response feasible; general replay's affordability filter is outside BM |

## Changing action sets: valid lemma, failed instantiation

Let `A = union_t A_t`, finite, and choose a retraction `r_t:A->A_t` fixing
`A_t`. For local loss `ell_t` and modification `F^t:A_t->A_t`, define

```
tilde ell_t(a) = ell_t(r_t(a))
tilde F^t(a)   = F^t(r_t(a)).
```

Every row of the Blum--Mansour transition matrix is a mixture of outputs of
`tilde F^t`, hence has support in `A_t`. If `p^t = p^t Q^t`, then
`p^t(A \ A_t)=0`. On that support `r_t` is identity, so both actual expected
loss and every transformed expected loss equal their unpadded values. Summing
preserves regret exactly. The choice of retraction outside `A_t` cannot affect
the played distribution.

Raw union padding is invalid. Assigning an unavailable action a special loss can
make it the best action, and an infinite penalty breaks boundedness. The test
suite contains the three-action counterexample and checks the retraction and
stationary-support steps with exact rationals.

This lemma requires a horizon-independent finite `A`. The proposed instantiation
used repository-native `Response` objects. Their `LedgerEffect` records contain
occasion-specific obligation identifiers, so the union size is `3T+5`: exactly
41, 77, 149, and 293 at the declared horizons. Substitution into Theorem 18
changes `sqrt(T N log K)` into `Theta(T sqrt(log K))`. The encoding is therefore
not the applicability bridge item 30 needs.

The repair is precise: define eight semantic action labels without ledger data,
decode a label against the current occasion to derive the response and ledger
effect, and prove that encoding/decoding preserves the local map, charge, and
regret. It must also keep each local lawful map closed on the labels. The current
tests persist the `3T+5` counterexample.

## Guards, leakage, and fixedness

Context is not compiled into the action label. Doing that would produce a large
state-action space and would still not solve causal access. It is compiled into
the history-indexed rule `F^t`, which Theorem 18 already permits. A comparator is
fixed ex ante when its guard, proposal function, policy suite, and declared
footprint are fixed before play. Later selection of a profitable guard would be
a different, hindsight-chosen comparator class.

The argument seal hides actual profitability from supplied arguments. The
preparation footprint excluded named `charges` and `accounts` tables but exposed
the data from which they are derived; this is a concrete defect in its structural
claim. The theorem-facing seal zeroes tariffs and removes accounts before guard,
proposal, or policy code runs. Tests change both real tariffs while holding
reasons fixed and obtain the same action map and a different loss vector; a guard
written to seek a positive tariff can see it through the old interface and cannot
through the sealed arguments. But an arbitrary Python callback can close over
the original history or tariff and bypass the seal; an exact test now exhibits
that. Profit independence is therefore an audit fact about the existing default
programs, not a capability guarantee for the callback type. An interpreted rule
language or a finite non-capture audit is the second missing interface condition.

## Scope boundary

The bridge covers the frozen item-30 environment. It does not cover:

- replay-prefix guards or endogenous filings, which make comparator consequences
  part of later context;
- suspension or another state transition by which an edit changes future losses
  or availability;
- a comparator class filtered after replay by affordability;
- bandit feedback without an estimator and a corresponding theorem;
- an infinite or dynamically hindsight-generated comparator class.

Those objects are policy/stateful regret problems, not ordinary Φ-regret under
this reduction. No neighboring framework is needed for item 30 because its
frozen configuration excludes them. Reinstating them is a later stateful online-
learning question.

## Next theorem/test

Item 29 remains open only on a bounded interface task: implement the fixed
eight-label encode/decode bridge, prove uniform `N=8` and regret preservation,
materialize and audit all nine programs, and state whether the target is expected
mixed loss or a sampled trajectory. Only then may item 30 instantiate Theorem
18's row-conditioned weights and stationary distribution. It must use the
theorem's `sqrt(N log K)` dependence, not plain exponential weights over nine
transformations or a `sqrt(log K)` bound.

Item 31 is unchanged. F4 did not block the audit: this round consumed the
ci-only preparation adapter and did not promote the disposable answerability or
docket implementations.

## Evidence status and non-results

The literature facts are source readings. The causal and padding components have
the derivations above and ten exact finite tests, including the two counterexamples.
They are not registered
claims and have not been ported to Lean. No learner, regret bound, asymptotic
rate, comparator coverage result, or recurring-failure retirement theorem was
established.
