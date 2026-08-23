# Afoundational normative record and inquiry

Status: **research memo; unregistered**. General positive statements are paper
derivations. The executable suite supplies finite witnesses, not a promoted
specification or theorem.

## Verdict

**Partial unification after temporal and scheduling repairs.** The role-parametric answerability kernel is
the correct account layer for inquiry liabilities. The proposed collapse is not
total. A due token is a historical trigger receipt before it becomes a
commitment, and an undocketed token needs a visible coverage debt. Rules,
service specifications, and tasks can share the identity-bearing commitment
machinery through tagged `Hold` and `Do` contents, but their semantic checkers
remain typed.

The three proposed record constructors are insufficient. `Root`, `Undertake`,
and `Account` omit empirical receipts, trigger accrual, service-specification
versions, and basis-loss events. The smallest surviving division is:

```text
L event: Observe(receipt, time)

R event:
  Seed(commitment, inductionReceipt)
  Undertake(act, grounds, licenseDerivation, accountIncidence, certificate)
  Accrue(dueToken, ruleVersion, receipt, serviceSpecVersion)
  Account(inputs, typedDisposition, successors, certificate)
  BasisLost(historicalUse, epoch, reviewOccurrence)
```

`R_n` and `L_n` are append-only histories. `View(R_n,L_n)` supplies standing
rules, current commitments, open issues, suspended items, coverage debts, and
the scheduler snapshot. Mutable-looking state is not rewritten history.

## 1. Record boundary

`L_n` contains world interaction receipts: actions, utterances, measurements,
testimony, query responses, and consequences. A receipt records what was
received or done and when. A normative interpretation of it is a defeasible
judgment in `R_n`. This prevents an empirical datum from carrying authority by
type.

For every normative act, three proof-relevant relations remain distinct.

| Relation | Question | Permitted source |
|---|---|---|
| grounds | Why this content? | receipts and earlier normative judgments |
| normative license | What entitled this kind of act? | standing authority in the pre-state |
| account incidence | Which old occurrence is being answered? | old identity-bearing commitments |

The existing certificate checker already supplies the pre-state discipline,
immutable undertaken receipt, declared dependencies, and rule-version closure.
The account DAG supplies input-scoped incidence, fresh/inherited separation,
typed closure, semantic transport, and basis-loss review. The new work adds
authority ancestry as a distinguished certificate projection and adds trigger
and service events around that kernel.

## 2. Authority genealogy

Let authority acts be a finite sequence. A seed occurrence may have no incoming
license edge only at initialization. Every later authority act has at least one
license parent whose occurrence index is strictly smaller. Grounds and account
edges do not count as license edges.

### No New Normative Roots

Under those hypotheses, every maximal backward license path from a post-seed act
terminates at a seed. At each edge the nonnegative occurrence index strictly
decreases, so a path is finite. A maximal endpoint has no parent and is therefore
a seed by the root restriction.

Strict pre-state ordering rejects self-licensing and simultaneous mutual
licensing. An empirical receipt listed only among grounds leaves a post-seed act
unlicensed. A rule installation cannot use the rule being installed because its
parent is not in the pre-state.

This theorem is genealogical conservation. It does not derive present content
from the seed. The grounds of a current act may consist entirely of later
receipts and revised judgments. It also leaves the checker grammar outside the
graph. Any substantive permission hardcoded into that checker is another
primitive normative expenditure and must be declared as such. The preferred
fixed checker enforces shape, version binding, scope composition, and account
grammar; substantive trigger and disposition rules remain versioned objects in
`R`.

## 3. Commitments, rules, and due tokens

The useful narrow waist is an occurrence with immutable identity and tagged
content:

```text
Commitment(id, Hold(judgment) | Do(task), meaningReceipt)
```

Rules and interpretations are `Hold` contents. Investigation, consideration,
review, response, and substantive performance are `Do` contents. Equal content
does not identify occurrences. Split, merge, delegation, suspension, closure,
and review use the existing per-input account law.

`May` and `Must` are rule modes, not complete semantics. A versioned rule also
needs a finite trigger program, output type, service specification where it
generates work, authority occurrence, checker version, and declared
dependencies. `May` licenses an act. `Must` emits a due token when its trigger
fires. The modes organize reason-responsiveness and inquiry generation without
requiring semantic closure under all implications.

A due token is not yet the owed commitment:

```text
DueToken(id, ruleVersion, receiptId, accruedAt, task, serviceSpecVersion)
```

It proves that the practice standing at accrual emitted a requirement. Atomic
generation also creates a coverage debt. Docketing replaces that debt with a
`Do(task)` occurrence whose `originDue` is the token. An explicitly authorized
terminal coverage account is another possible disposition. Silent absence is
not.

## 4. Temporal semantics

“Event time” must name a record time, not an unobservable world time. A step is
ordered as follows:

1. append the empirical receipt to `L`;
2. evaluate finite `Must` triggers against the rule view fixed for that receipt;
3. append due tokens and coverage debts atomically;
4. admit later normative amendments against the pre-amendment state;
5. derive the new view.

This ordering makes a receipt and repeal in one transaction unambiguous: the
then-standing rule accrues the token, while repeal governs later receipts. A
revision committed before the receipt changes the rule view first and therefore
changes accrual.

Delayed recognition is different. The preferred base semantics accrues when a
receipt becomes available to the practice, under the rule then standing. A rule
may explicitly inspect a receipt's world-time field and generate a retrospective
task, but that is a substantive rule, not a checker default. Changed evidence or
discovered interpretive error does not delete a token. It supplies grounds for a
typed disposition or triggers basis-loss review of the undertaken accrual basis.

An explicitly authorized retroactive rule can change the current treatment of
old tokens only through input-scoped accounts. It cannot make the historical
accrual event absent. Settlement events remain basis-free and incorrigible;
normative uses of them remain reviewable under the existing distinction.

### No Retroactive Evasion

Assume due-token events are append-only and current docket status is derived only
from a token plus its account descendants. Repealing or replacing its generating
rule appends a rule event and does not remove either object. Induction over later
events therefore preserves the token and either its live/debt frontier or an
explicit terminal account. The result is history preservation, not a ban on
authorized cancellation.

## 5. Coverage and certified service

Three notions do not collapse.

**Docket coverage** asks whether every token is represented by an identity-
bearing liability, a visible coverage debt, or a typed terminal coverage
account. Atomic debt creation makes this prefix safety. A deadline for docketing
adds a bounded processor hypothesis. Eventual docketing adds fairness and
serviceability.

**Service coverage** is liveness. Once docketed, No Forgotten Inquiry follows
from the existing No Forgotten Liability result: a `Do` occurrence retains an
ancestry-linked live/suspended frontier or input-scoped closure. Eventual service
requires capacity/load assumptions. With two arrivals and capacity one per
step, backlog grows by one per step, so an unconditional deadline is false.

**Certified service** is a typed terminal disposition. Each inquiry occurrence
pins `sigma_ell`, the service specification standing at its creation or explicit
migration. A certificate must name the occurrence and that version and supply
adequate evidence. Rebinding an old occurrence to an empty new specification
does not discharge it. One investigation may supply shared evidence to two
liabilities, but both old inputs need separate adequacy and account edges.

Progress functions `f_ell(psi) in [0,1]` are scheduler inputs. They do not by
themselves close an occurrence at value one; closure still requires a certificate
against `sigma_ell`. Delay functions encode scheduling urgency or charge, not
objective normative importance. Any priority or delay semantics is a versioned
normative object handed to the scheduler in a finite snapshot.

## 6. Exact restricted scheduler bridges

### 6.1 Set Cover with Delay

For a restricted deterministic inquiry system, let task kinds form a finite
universe `E`. Each query action `q` has a fixed positive cost and a fixed covered
subset `S_q`. Due tokens arrive over time on elements of `E` and have
nondecreasing accumulated delay functions. Executing `q` serves every then-
pending token whose element lies in `S_q`; later arrivals require a later
execution.

The translation to Set Cover with Delay is the identity map:

```text
task kind       -> element
query action    -> purchasable set
action cost     -> set cost
due-token event -> request arrival
urgency charge  -> accumulated delay
execution time  -> set-purchase time
```

For every schedule, the service time of each token is the same first covered
purchase time. Purchase costs and each token's delay are copied term by term, so
the total objective is equal. The finite test recomputes this equality with
`Fraction` values. The paper's model allows repeated purchases and does not make
past purchases serve future requests, matching this interface.

The paper permits a request never to be served, with service time infinity; its
footnote explicitly notes that the model is more general than mandatory service.
A finite terminal delay therefore permits permanent nonservice. Divergent delay
is necessary for the elementary one-request liveness argument and is not
sufficient under arbitrary background load.

The proposed competitive-service corollary is false without a load bound. At
horizon `T`, a policy can pay unavoidable background cost `T`, ignore one focal
token with delay `T`, and have cost `2T`; a comparator pays `T+1`. The starving
policy is two-competitive for every `T`.

The repaired statement is: if `Cost_A(T) <= alpha Cost_OPT(T)+beta`, a comparator
has `Cost_OPT(T) <= B` uniformly in `T`, and the delay of an unserved focal token
diverges, then the token is eventually served. Otherwise the algorithm's cost
eventually exceeds `alpha B+beta`. A marginal or isolated-request competitive
guarantee can replace the uniform comparator bound.

Source checked: Yossi Azar, Ashish Chiplunkar, Shay Kutten, and Noam Touitou,
“Set Cover with Delay—Clairvoyance Is Not Required,” *ESA 2020*, LIPIcs 173,
Article 8, DOI `10.4230/LIPIcs.ESA.2020.8`. Borrowed: the repeated-set-purchase
request/delay objective and its nonclairvoyant setting. Not borrowed: a
normative interpretation, certification, or unconditional service theorem.

### 6.2 Submodular ranking and MLSC

For a fixed finite docket, let each inquiry action be a vertex and let context
switching be a symmetric metric with root `r`. Each occurrence has a pinned
normalized monotone submodular progress function `f_ell` on the set of visited
actions. It is covered at the first path length where `f_ell=1`. The sum of
liability cover times is exactly the Minimum Latency Submodular Cover objective.
With unit transition costs, a path is an ordering and this is submodular ranking.

This bridge excludes changing dockets, repeated stateful actions, nonmetric
switching, and mutable objectives. Intrinsic action costs require a valid metric
encoding or a different model. Complementarity is a direct failure: if progress
is one only after both `a` and `b`, the marginal value of `b` rises after `a`, so
submodularity fails.

Source checked: Sungjin Im, Viswanath Nagarajan, and Ruben van der Zwaan,
“Minimum Latency Submodular Cover,” *ACM Transactions on Algorithms* 13(1),
Article 13 (2016), DOI `10.1145/2987751`. Borrowed: multiple normalized monotone
submodular objectives, metric path, and sum of cover times. Not borrowed: dynamic
arrivals, certification, or a claim that inquiry progress is generally
submodular.

### 6.3 Adaptive stochastic inquiry

Golovin–Krause applies when there is a finite fixed item set, fixed item states,
a realization `phi`, a known prior over realizations, and a fixed utility
function satisfying the relevant adaptive monotonicity and adaptive
submodularity hypotheses. Their coverage definition requires maximal utility
for every realization consistent with the observation history, not merely for
the true realization. Self-certification is an instance property under which
achieving the true maximum immediately proves that fact across the consistent
realizations.

This supplies a useful model for service certification only when the pinned
service specification compiles into that fixed realization/utility model. It is
not a legitimacy axiom. Conditional synergies violate diminishing returns, and
queries that alter the underlying realization fall outside the framework. A
rule amendment or service-specification migration therefore requires a new
scheduler instance and an account transition; it cannot be treated as another
observation in the old instance.

Source checked: Daniel Golovin and Andreas Krause, “Adaptive Submodularity:
Theory and Applications in Active Learning and Stochastic Optimization,”
*Journal of Artificial Intelligence Research* 42 (2011), 427–486,
arXiv `1003.3967`. Borrowed: fixed-realization adaptive coverage,
self-certification, and tractability conditions. Not borrowed: a Bayesian
foundation for normativity or guarantees under mutable objectives.

Guillory–Bilmes gives a non-Bayesian worst-case class: a finite hypothesis class,
known query-to-valid-response relation, adversarial response consistent with the
unknown target, and a known monotone submodular objective for each hypothesis.
This is closer when outcomes are adversarial rather than sampled from an
endorsed prior. It still assumes a fixed target in the hypothesis class, a fixed
response relation, noiseless consistency, and pointwise submodular objectives.

Source checked: Andrew Guillory and Jeff Bilmes, “Interactive Submodular Set
Cover,” *ICML 2010*, 415–422, arXiv `1002.3345`. Borrowed: the worst-case
query/response coverage class. Not borrowed: adequacy of the hypothesis class or
normative authority for its objective.

## 7. Evaluators, legitimacy, and the compiler

An external starred evaluator remains useful for separation tests. The finite
witness makes an evaluator-relative demand true while no inherited `Must` rule
generates it. This disagreement is expected: evaluator adequacy and internal
generation are distinct notions. The preferred positive model spends primitive
normativity at the seed and follows seed-descended rule authority thereafter.

Actual-run integrity consists of accepted authority genealogy, immutable
receipts, explicit accrual, account conservation, basis-loss review, and any
separately assumed liveness/certification properties. A controller can shape the
rule evolution while every one of these holds. Counterfactual non-capture remains
the coupled-run factorization/hyperproperty from the existing legitimacy work.

The current view of `R_n` can expose standing/applicable liabilities and the
typed credal-bearing fragment to an operative compiler. This round does not
construct `R -> O`. The joint-semantics-to-credal gap remains open. Existing
`O -> C -> K -> E` feasibility, projection, funding, and traderization work is
unchanged; market force establishes neither genealogy nor inquiry adequacy.

## What is not established

No claim is registered or kernel-checked. The general authority, accrual,
coverage, and embedding results are paper derivations with finite executable
witnesses. The round does not construct a substantively sound seed, complete
trigger language, fair scheduler under general load, service-specification
compiler, adaptive-submodular inquiry domain, counterfactual non-capture proof,
credal compiler, or end-to-end normative learner. It does not show that
genealogical continuity is philosophical justification or that internal
legitimacy tracks an external evaluator.
