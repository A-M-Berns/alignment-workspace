# Theory 12: the parametric composite, and the constructions

This part does three things. It records the correspondence between the previous
consolidation's condition bundle and the interface clauses of Theory 11,
including the conditions with no counterpart. It restates the conditional
composite over **any engine satisfying the relevant clauses** rather than over
one named bundle. And it constructs the empirical channel and the two-engine
instance that make the quantification non-empty and discharge the conduct
clauses' obligations.

Every symbol used here is defined here or in Theory 11.

## 1. The bundle, restated

The previous consolidation's conditional cap is stated over one named condition
bundle. Restated in the vocabulary of Theory 11, and with its own symbols
renamed to this monograph's, it assumes: a computable deductive process; that
each date publishes before demand a rational compact convex region; a rational
witnessed reference and a fixed positive core coefficient with the core
condition **against the ambient simplex**; coherent extension of the retained
world mixture to fresh queried sentences; a drift limit summing to a finite
total; a constrained quote whose selection errors sum to a finite total; a
rational prefix-causal clock and an aggregate downside limit of two; and an
aggregate trading field with a declared dominance property. Its conclusion is a
horizon-uniform cap on gain in every plausible world, with the inherited
downside limit preserved.

The composite of the source tree inherits that bundle wholesale, so its own
statement is available only if every bundle condition is separately supplied.
Theory 11 describes a *class* of engines instead. The correspondence between the
two descriptions is the subject of §2.

## 2. The correspondence, and its findings

**The correspondence is not an identity.** {#NL-SI-M1}
**Status: MACHINE-CHECKED (stated finite scope).** Of the nine condition rows,
one is supplied by the interface clauses, two are strictly stronger than any
clause needs, three have no counterpart at all, two are incomparable, and
exactly one is a clean correspondence. Twelve of the eighteen clause texts are
never exercised.

| row | bundle condition | clause(s) | relation |
|---|---|---|---|
| M1 | a computable deductive process | J1, C1-logical | implied by the clauses, reading declaration as effective presentation |
| M2 | publication before demand of a rational compact convex region | — | **no counterpart** |
| M3 | a fixed positive core coefficient, core condition against the **ambient** simplex | P1 | **bundle strictly stronger** |
| M4 | coherent extension to fresh queried sentences | — | **no counterpart** |
| M5 | a drift limit with finite total | — | **no counterpart** |
| M6 | a constrained quote with selection errors summing to a finite total | T1 | **neither direction** |
| M7a | a rational prefix-causal clock | C2, C3 | **neither direction** |
| M7b | an aggregate downside limit of two | P2 | equivalent modulo the declared constant |
| M8 | an aggregate trading field with the declared dominance property | P4 | **bundle strictly stronger** |

Clauses never exercised by the bundle: J2 — the bundle has **no exclusivity
formulation at all**, so nothing in it prevents a variable being settled twice;
J3, since the bundle is stated inside one fixed language; C1-empirical, its
channel being purely deductive; C3, relating no downstream deadline to an
upstream horizon; P3, quantifying over an infinite enumerated family and never
bounding what is live per date; T1, the coherence tolerance as distinct from
M6's solver budget; T2, having no notion of who carries a breach; F1 through F4;
and the proof-carrying requirement, its process emitting sentences with nothing
asking it for derivations.

**Where the strictness bites.** {#NL-SI-M2} **Status: PROVED (single
derivation).** M3 is not merely a demanding version of P1. Under settlement its
ambient reading is unsatisfiable.

**Proof.** Immediate from `NL-SI-A1`: once one non-trivial settlement is
recorded the endorsed region lies in a hyperplane while a positive homothet of
the ambient simplex spans the simplex's affine hull, so containment fails for
every positive coefficient. A composite stated over the ambient reading
therefore has an antecedent nothing inhabits once anything is settled. `square`

**M6 is a different quantity from T1.** {#NL-SI-M3} **Status: PROVED (single
derivation).** The bundle's error budget and the tolerance clause bound
different things, and neither implies the other.

**Proof.** T1 bounds the incoherence of the engine's *prices*: the distance from
the displayed price assignment to the coherent assignments. M6 bounds the
cumulative error of the compiler's *chosen quote* against the constrained
optimum. Exhibit each direction. Prices may be exactly coherent while a solver
selects a suboptimal feasible quote at every date, giving incoherence zero and
solver error positive. And a solver may select the exact constrained optimum at
every date while the prices it is optimizing against are incoherent, giving
solver error zero and incoherence positive. So neither bounds the other, and
the bundle carries only the second while the interface carries only the first.
`square`

## 3. The compiler contract

The four conditions with no interface counterpart are not properties of a
world-channel, so they cannot become engine clauses without misattributing them.
They are conditions on the **compiler** standing between engine and mechanism,
and are named here as one block. The name is adopted; the block is:

1. **publication before demand** — each date publishes its rational compact
   convex region prefix-causally;
2. **coherent extension** — the retained world mixture extends coherently to
   fresh queried sentences;
3. **a summable drift schedule** — reference drift is limited by a computable
   schedule with finite total;
4. **a solver budget** — the constrained quote's selection errors sum to a
   finite total; by `NL-SI-M3` this is not T1.

With the block named the composite reads in three parts: **the engine satisfies
the interface, the compiler satisfies its contract, and then the cap holds.**

## 4. The adequacy inequality, in general form

Theory 11's C3 is discharged here, on the channel §5 constructs. Fix a per-date
service **capacity** `k > 0`. Each admitted ripe query has an admission date
`a`, a deadline `d`, a declared service work `W`, and upstream procedures whose
greatest declared horizon is `H`. Write `rel = a + H` for the **release date**:
the earliest date downstream service may begin.

**Adequacy** is the conjunction of:

- **per query**: `a + H + ceil(W / k) <= d`; and
- **per window**: for all dates `t1 <= t2`,
  `sum { W : rel >= t1 and d <= t2 } <= k (t2 - t1 + 1)`.

**Adequacy is exactly feasibility.** {#NL-SI-AD1} **Status: PROVED (single
derivation).** Suppose work within a date is divisible across queries. Then
every ripe admitted query meets its deadline under earliest-deadline-first
service if and only if the window inequality holds.

**Proof.** *Necessity.* Fix `t1 <= t2`. Every query with `rel >= t1` and
`d <= t2` can be served only during dates `t1` through `t2`, since service
cannot begin before release and must finish by the deadline. Those dates supply
`k (t2 - t1 + 1)` units in total. If the demand exceeds that, some query in the
set is unfinished at its deadline under *every* schedule, in particular under
earliest-deadline-first.

*Sufficiency.* Suppose the window inequality holds and, for contradiction, that
earliest-deadline-first misses some deadline. Let `t2` be the first date at
which a query is unfinished past its deadline, and let `t1` be the latest date
at or before `t2` such that the server is idle at `t1 - 1`, or that some query
served in `[t1, t2]` was released at `t1`, taking `t1` minimal with the property
that the server is busy throughout `[t1, t2]` on queries released at or after
`t1`. Such a `t1` exists: walk back from `t2` while the server is continuously
busy on queries with release at least the current candidate, which terminates
because releases are finite in number. Throughout `[t1, t2]` the server is busy
and, by the earliest-deadline-first rule and the choice of `t1`, works only on
queries with release at least `t1` and deadline at most `t2` — a later-deadline
query would have been preempted by the missed one. So the work completed in the
window is `k (t2 - t1 + 1)` and yet is insufficient, meaning the demand of that
set exceeds the supply, contradicting the window inequality.

The per-query inequality is the single-query case of the window inequality
together with the observation that `ceil(W/k)` dates are needed to supply `W`
units at rate `k`; it is retained separately because it localizes a violation to
one query. `square`

**The inequality is discriminating.** {#NL-SI-AD2} **Status: MACHINE-CHECKED
(stated finite scope).** On the constructed channel with two queries of service
work `2` and upstream horizons `2` and `3` against capacity `1`, adequacy holds
at deadline `8` and every deadline is met; at deadline `4` both inequalities are
violated — per query, `0 + 3 + 2 > 4`; per window, `[2,4]` must serve `4` and
supplies `3` — and a deadline is missed. Two queries of work `2` each, both
released at `0` with deadline `4` and capacity `1`, are adequate query by query
and jointly infeasible, and the window inequality catches exactly that.

**On a purely logical docket the inequality is vacuous.** {#NL-SI-AD3}
**Status: PROVED (single derivation).** With no empirical upstream there is no
horizon term, and the constraint is coverage of nothing.

**Proof.** C1 promises no rate on the logical channel, so a query whose upstream
is purely logical has no declared `H`. The per-query inequality then reads
`a + 0 + ceil(W/k) <= d`, which is a statement about downstream service alone
and not about the engine, and the window inequality likewise involves no engine
quantity. The work of keeping such a query honest is done entirely by C2's
tolling. This is coherent design and not coverage: C3 constrains the empirical
channel only, and should not be read as securing adequacy for logical
settlement. `square`

## 5. The constructed empirical channel

The channel is built on declared procedures with outcome spaces and horizons.

**Directional funding is unconstructible.** {#NL-SI-K1}
**Status: NECESSITY WITNESS.** The request key type has no field an outcome
could occupy, and the map from funding intents to keys forgets the direction.

**Witness.** The key carries exactly `(target, procedure, funder, requested
date, scheduled date)`. Construct the key from a funder's intent, which includes
an intended outcome: the outcome argument is dropped, since there is nowhere for
it to go. Consequently two funders intending opposite settlements of one
question write the **same key**, and the image of the intents of one question
under key construction is a single point. Directional funding is therefore not
forbidden by a check that could be omitted; it is inexpressible. `square`

**The executor cannot read the book.** {#NL-SI-K2} **Status: NECESSITY
WITNESS.** The execution function takes the procedure, the date, and the world,
and nothing else.

**Witness and disclosure.** The signature admits no book parameter and no funder
parameter, so no path from book or purse to a settled value can be written in
this construction. Performativity remains available and is deliberately
permitted: an agent whose actions change the world changes the world argument,
and the settlement faithfully reports the world the agent helped make.

**This is a disclosure about this construction, not a proof of the faithfulness
axiom.** The axiom quantifies over every engine; a signature constrains only
this one. What the typing buys is that no later edit can introduce the
dependence without changing a signature the verification reads. `square`

**A settlement event carries no answerability columns.** {#NL-SI-K3}
**Status: NECESSITY WITNESS.** The event type has no basis, stake, charge or
objection field, checked structurally rather than by convention.

**The three downstream effects, exhibited.** {#NL-SI-K4}
**Status: MACHINE-CHECKED (stated finite scope).** On the constructed channel a
settlement constrains — the credal interval of the bridged world claim moves
from `[0,1]` to `[1,1]` once the settlement's equality and the declared
valuation enter; pays — an instrument referencing the variable with payoff `3`
at the settled value resolves in exactly one transfer of `3` from counterparty
to holder; and grounds — an endorsed bridge warrant to a world claim yields
citable grounds, while an unendorsed one yields none.

**Clock discipline.** {#NL-SI-K5} **Status: MACHINE-CHECKED (stated finite
scope).** The ripeness gate refuses a query whose deadline no declared horizon
reaches, and charges nothing for the refusal. A query whose upstream is the
rateless channel is admitted and tolled rather than refused. A procedure
settling past its declared horizon tolls the clocks it touches by exactly the
overrun and charges the book nothing.

## 6. Conduct, discharged

The conduct clauses F3 and F4 are **new objection types**: the previous
consolidation contains no insider, blackout, or common-source machinery. Its
conduct family's displayed member is a cross-component transfer objection — a
public fence declaration, a typed transfer, upheld exactly when the transfer
crosses the declared fence, vacuous when no fence is declared. F3 and F4 are
built in that family's shape and their obligations are discharged here.

**The conduct witnesses fire and their controls do not.** {#NL-SI-K6}
**Status: MACHINE-CHECKED (stated finite scope).**

- *Stopping neutrality.* A precommitted rule is a checkable property of a
  request: the declared stop is present and the realized stop equals it. Its
  neutrality content is checked by replay — the stop date is identical under two
  worlds returning opposite outcomes, so the rule creates no directional bias in
  what gets certified.
- *Probe blackout.* Grounds are produced when the funder takes a fresh position
  on its own request's target inside the window from funding to settlement, and
  are **not** produced for a position outside the window, a position by another
  actor, or a stale position. Three controls, all silent.
- *Funder provenance.* Grounds are produced when one purse appears in the
  funding profile of every premise settlement of one conclusion, and not when
  two distinct purses do.

Both new types carry declared judge footprints over the registered settlement
tables and are judged **through the grammar verifier** of Theory 7, not by
direct call, so a judge reading outside its declared footprint would have its
verdict withheld. `square`

## 7. Two engines, one mechanism

**Redundancy never reaches the settled record.** {#NL-SI-E1}
**Status: MACHINE-CHECKED (stated finite scope).** Two procedures disagreeing
about one world claim produce no settled-record conflict, and the disagreement
appears in the answerable layer.

**Witness.** Thermometer A returns `warm` and thermometer B returns `cold`, both
at date one. These are distinct procedures, hence distinct report variables,
hence two settlement events that write-once cannot bring into conflict: nothing
in the settled record is contradictory and no clause is breached. Each reaches
the world claim through an endorsed bridge warrant, one supporting and one
undercutting. Compiled into the book, the two warrants give `p >= 3/4` and
`p <= 1/4` for the claim, so the docket polytope is empty and the existing
sure-loss surface reports against the **book**. The engines are untouched. This
is exactly what J2's redundancy provision asserts. `square`

**Breach is isolated by channel.** {#NL-SI-E2} **Status: MACHINE-CHECKED
(stated finite scope).** A tolerance breach in the empirical channel quarantines
that channel and leaves the other running.

**Witness, with the two tolling causes kept apart.** After the breach the
empirical channel's clocks are frozen and tolled *by the breach*; the logical
channel's are neither frozen nor tolled by the breach, though they carry the
tolling the ripeness clause imposes on the rateless channel regardless. The
separation is load-bearing: reporting a single tolling flag would let that
standing tolling masquerade as a failure of isolation. `square`

**The purse composes only inside its fences.** {#NL-SI-E3}
**Status: MACHINE-CHECKED (stated finite scope).** Each engine declares its own
downside limit; total exposure is limited by the fenced sum exactly when no
transfer crosses between provenances.

**Witness.** With limits `0` and `2` the fenced sum is `2`, and recorded
exposures within each provenance's own limit satisfy it. A transfer from the
logical account to the empirical account crosses a declared fence and fires the
existing cross-subsidy objection; a transfer inside one provenance's account
family does not; and a pooled system declaring no fence has nothing to cross.
A fence around a single account rather than a provenance's family would make
every movement a crossing and the objection would carry no information. `square`

## 8. The parametric composite

**The composite, quantified over engines satisfying the clauses.** {#NL-SI-X1}
**Status: PROVED-CONDITIONAL (conditions listed).** Let `K` be a finite flow
mechanism and challenger class satisfying the hypotheses the source composite
requires of them, together with that composite's mechanism-side hypotheses. Let
`e` be a settlement engine with declaration `E` and finite record prefix `R`
such that:

**(a)** `e` satisfies the checkable clauses J1, J2, J3, C1-empirical, C2, C3,
P1, P2, P3, P4, T1, T2 and the proof-carrying requirement on `R`;
**(b)** hypothesis objects are supplied for the declared clauses C1-logical,
P1-persistence, and P4-semantics;
**(c)** the compiler contract of §3 is supplied, all four conditions;
**(d)** hypothesis objects are supplied for the three audited conditionals:
consistency of the declared theory, the core minimum or the clipping adapter,
and a working tolerance.

Then every conclusion of the source composite holds, and in particular for every
represented world and every horizon the operative-force cap

    quote-error-total / theta_min  +  kappa ( risk-limit + movement cap )

holds, with `theta_min` the engine's certified core minimum,
`kappa = (1 - theta_min)/theta_min`, and the movement cap the source recursion
evaluated at the potential limit on active-book changes.

**Proof.** By substitution. The source composite's hypothesis of a uniform
positive core on every activated endpoint is discharged by (a)'s P1 — which by
`NL-SI-A3` is the statement that a reference admitting the declared coefficient
exists at each recorded date — together with (b)'s persistence hypothesis, which
extends it past the prefix. Its worldwise aggregate risk guard is discharged by
P2, whose declared downside limit is that guard. Its quote-error hypothesis is
(c)'s solver budget and its drift hypothesis is (c)'s drift schedule; neither has
an interface counterpart, which by `NL-SI-M1` is why they are hypotheses here
and not clauses. The remaining hypotheses are mechanism-side and are carried
unchanged. With every hypothesis in place the source composite applies verbatim
and its cap is the displayed one with the engine's certified coefficient
substituted.

**Nothing new is proved.** What changes is that the antecedent is a predicate
over a class of engines and is *evaluated* rather than assumed. `square`

**The antecedent has thirteen hypothesis objects, each load-bearing.**
{#NL-SI-X2} **Status: MACHINE-CHECKED (stated finite scope).** Three declared
clauses, four compiler-contract conditions, three audited conditionals, and
three mechanism-side hypotheses. Omitting any one yields no cap at all and names
the omission; the evaluator reports no number on an antecedent it has not
earned.

**The composite is not vacuous.** {#NL-SI-X3} **Status: MACHINE-CHECKED (stated
finite scope).** The reference engine of `NL-SI-W1`, with quote-error total `0`,
risk limit `2`, ordinary movement `0` and one book change, satisfies the
antecedent once the thirteen objects are supplied, and the cap evaluates to
exactly `30` at core minimum `1/4`. At `1/10` it is `198`. The cap grows without
limit as the core minimum shrinks, which is the content of P1's warning that
force evaporates as conviction decays. A declared minimum the record cannot
support — anything above `2/5` on that prefix, by the closed form `NL-SI-A5` —
yields no cap at all rather than a worse one.

**The instance corollary.** {#NL-SI-X4} **Status: PROVED-CONDITIONAL
(conditions listed).** Let the candidate pair be as the reading audit
`NL-SI-SIM` describes it. Then the parametric composite applies to it, with the
cap instantiated at the declared core minimum, provided exactly three
conditionals: consistency of the declared theory; either a stably satisfiable
core minimum or the clipping adapter; and a working tolerance, which for this
pair is available only by the certification-layering route of `NL-SI-T3`.

**Standing of this corollary.** Its antecedent rests on a **reading audit**, not
on a construction: nothing in this package builds the pair, and `NL-SI-SIM` is
labelled accordingly. Each of the three conditionals is individually required
and is refused by name when absent. This is the honest current form of the
witness theorem's payoff, and it is not the witness theorem. `square`

## 9. What this part does not establish

The composite is a substitution and inherits every hypothesis the source
composite inherits; it proves nothing the source did not, and it does not
establish the composite guarantee, since satisfying the interface is that
conditional's antecedent. The instance corollary is not the witness theorem. The
constructions are displayed finite instances: they show the clauses can be
discharged, not that any interesting engine discharges them. The typed
obstructions are disclosures about these constructions and leave the assumed
residues exactly where Theory 11 left them.
