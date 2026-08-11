# Settlement interface — theorems and constructions

This pass moves the settlement interface from a definition to a formal object
that theorems quantify over, and builds the constructions that make the
quantification non-empty. The closing-phase report is archived at
`archive/ROUND_REPORT_closing_phase.md` with a manifest entry; its dispositions
stand.

The interface draft and its witness audit are **inputs and stay outside this
tree**. Neither was copied in and neither is modified. The audit's own note
gives the reason — its central term for the logical residue is retired
vocabulary here — and the same gate is why this document says *incoherence*,
*downside limit* and *core minimum* where the interface says something else.
Clause texts are quoted verbatim inside `src/settlement_interface.py`, with the
two retired nouns bracketed at the point of substitution so the edit is visible
rather than silent (`DEVIATIONS.md` 58, 65).

## What landed

| package | status |
|---|---|
| **WP-0** the interface as a formal object | **complete** — `src/settlement_interface.py`, 36 tests, `NL-SI-0` |
| **WP-1** the incoherence functional and the tolerance-robust docket | **complete** — `src/coherence.py`, 23 tests, `NL-SI-1` … `NL-SI-4` |
| **WP-2** the mapping check and the parametric composite | **complete** — `src/parametric_composition.py`, `MOVING_INTERFACE_MAP.md`, 24 tests, `NL-SI-5` … `NL-SI-7` |
| **WP-3** the core minimum under contraction | **complete** — `src/core_geometry.py`, 21 tests, `NL-SI-8` … `NL-SI-11` |
| **WP-4** the empirical channel, constructed | **complete** — `src/settlement_channel.py`, 33 tests, `NL-SI-12` … `NL-SI-14` |
| **WP-5** two engines, one mechanism | **complete** — `src/two_engines.py`, 24 tests, `NL-SI-15` |

Reserved and not approached: the deduction-budget clause and funding-responsive
deduction; the coherence modulus; everything in the inquiry and learning tracks.
Two boundary contacts are noted at the end.

---

## WP-0 — the interface as a formal object

Eighteen clause texts — the interface's sixteen lettered clauses plus the
logical residue, with completeness written out once per channel — carried
verbatim, and **twenty predicates** over them, each of exactly two kinds.
**Checkable**: a computable predicate over declared engine data and a finite
record prefix, returning obstructions. **Declared**: a hypothesis object
carrying its own statement, holding exactly when a matching object is supplied.

Seventeen predicates came out checkable and three declared — logical
completeness, the persistence of the core minimum, and the semantics of the
named certificate type. The count exceeds the clause count because three
clauses split across the line rather than falling on one side, which was not
anticipated: completeness splits by channel, the enforcement clause splits into
a per-date program and a persistence claim (below), and the certificate clause
splits into naming a type and that type's semantics holding.

The split is the honesty mechanism: an engine that satisfies the interface has
been checked *plus* a printed list of what nobody checked, and
`InterfaceReport.leaned_on` is that list.

The reference engine — a finite lookup-table pen, declared horizons, a refusing
purse — satisfies all seventeen checkable clauses, and its three declared
clauses report as **failing** until hypothesis objects are supplied. That is the
non-vacuity witness, discharged by construction rather than by a stand-in.

## WP-1 — the incoherence functional

The audit established that the tolerance clause governed an undefined quantity.
It is now defined as the minimal uniform distance from the displayed prices to
the coherent assignments, computed by one exact-rational linear program.

**The normalization is forced rather than chosen.** Each priced row is a
sentence indicator with `0/1` coefficients whose expectation spans the whole
unit interval, so a value of one is a genuine extreme. And the certificate's
price-row multipliers carry total absolute mass at most one — not a convention
but the tolerance column of the dual system. A reported excess and a declared
schedule are therefore the same units, and the comparison that decides a breach
is a comparison rather than a units error.

The displayed instance is tight and hand-checkable. Three worlds, sentences `A`
and `B` overlapping at one world with `C` their conjunction, priced at
`9/10, 9/10, 0`. Every assignment satisfies `A + B - C = 1` while the prices
demand `9/5`; the excess `4/5` spreads over three rows, and the functional
returns exactly **`4/15`**. The extracted certificate is `(1/3, 1/3, -1/3)` with
mass exactly one and excess exactly `4/15` — tight, not merely valid — and it is
re-verified by an independent program rather than read back from the extraction.

**Two polytopes, kept apart.** The functional measures the *engine* against
logic plus pins. The robust interval and merits certificate measure the *book*
against book plus pins with the tolerance inflation. This is load-bearing and
carries its own witness: a book whose endorsements are jointly infeasible with
the pins, around prices that are exactly coherent, scores zero incoherence.
Conflated, the same instance would read as an engine breach and would toll the
mechanism's clocks where it should charge the party that endorsed the pair —
the opposite respondent and the opposite consequence (`NL-SI-1B`).

The reduction at tolerance zero is a theorem and not a remark: the relaxed
constraint list is elementwise equal to the exact one, so the robust forms *are*
the exact forms. Pins and the simplex are never relaxed at any tolerance.

**Non-vacuity** is the strict-separation check. On the displayed two-sentence
book the robust lower bound on the target is `3/5 - tolerance` against a
threshold of `1/2`, so the merits certificate clears exactly while the schedule
is at most **`1/10`** and fails above it. At tolerance one the interval
degenerates to the unit interval and nothing ever clears — the audit's
soundness-versus-usefulness finding, as a computation.

**The layering** attributes every breach, witnessed both ways, and supplies the
audit's rescue: an engine certifying the maximal tolerance still permits a
working one, declared by the book, at the price of the book carrying the
liability as a chargeable position.

## WP-2 — the mapping, and the theorem that consumes the interface

`MOVING_INTERFACE_MAP.md` is the table. Summarised over its nine rows: one
condition is supplied by the interface, two are strictly stronger than any
clause needs, three have **no counterpart at all**, two are incomparable, one
corresponds cleanly — and twelve of the eighteen clause texts are never
exercised. Four conditions end up carried as explicit hypotheses of the
composite: the three with no counterpart, plus the solver-error budget, whose
adjacent clause does not supply it.

The row that matters is the bundle's fixed-core condition. It is not merely a
demanding version of the enforcement clause — read against the ambient simplex,
as the bundle states it, it is *unsatisfiable* under settlement (WP-3). A
composite stated over that reading has an antecedent nothing can inhabit once
anything is settled.

**The parametric composite** restates the corpus's conditional composite over
any engine satisfying the relevant clauses. It is a **substitution**, and the
ledger row says so: each inherited hypothesis is discharged by a named clause or
carried as a named hypothesis object, and the conclusion is the corpus's
unchanged. No new mathematics is claimed.

What the substitution buys is that the antecedent is *evaluated*. The theorem
returns no bound at all when any hypothesis is absent, and names the missing
one; each of the thirteen hypothesis objects is individually load-bearing, which
is checked by omitting them one at a time. On the reference engine with the
declared parameters it yields the corpus bound, `30` at a core minimum of `1/4`.
A declaration the record cannot support — anything above `2/5` on that record —
is not a slightly worse bound but no bound, and the check says which clause
failed.

**The instance corollary** states the audited pair's case with exactly the three
named conditionals: consistency of the declared theory, a stable core minimum or
the clipping adapter, and a working tolerance. Each is individually required and
refused by name when absent. The disclosure travels with the result: the pair
inhabits its clauses **by reading, not by construction**, nothing in this tree
builds it, and its working tolerance is available only by the layering route.

### Proposed clause revision — for the interface's author

The enforcement clause's character changes under this work, and the interface
document is deliberately **not** treated as amended. The restatement is offered
here for adoption or refusal:

> **(P1) Enforcement minimum, restated.** The engine certifies a core minimum
> `theta_min > 0` for its varying core, read **relative to the post-settlement
> feasible simplex** rather than to the ambient simplex. At each date the
> mechanism checks satisfiability of the declared minimum by linear program over
> the admissible-reference region; where the region is non-empty the reference is
> clipped to it, and where it is empty the condition is a detected breach with
> the declared consequence **quarantine of operative force**, handled by the
> breach clauses. The certified commitment is thereby verifiable at each date.
> What remains assumed, and is not discharged by the per-date check, is
> **persistence**: that the declared minimum keeps being satisfiable as
> settlement contracts the region.

Two things recommend it. The ambient reading it replaces is unsatisfiable under
settlement, so the clause as written cannot be honoured by any engine once a pin
lands. And the split narrows the open residue: what was one open question
becomes a per-date program plus a strictly smaller open question about the
infimum over time.

## WP-3 — the core minimum under contraction

**The ambient reading voids on the first exact pin**, for every positive
coefficient. A pin is an equality, so the endorsed region lies in a hyperplane,
while the homothet of the ambient simplex keeps the simplex's own dimension. The
two-sentence witness is displayed, and a three-world companion confirms it where
the post-pin region is still a segment — so the failure is not an artifact of a
region collapsing to a point. Recorded as a **NECESSITY WITNESS** for the
relative reading (`NL-SI-8`).

**The relative reading transports across an independent pin.** Independence is
checkable and turned out to be the natural notion: the pin is independent when
the *incumbent reference confirms it*. The proof is two lines — the post-pin
simplex sits inside the pre-pin one, and the reference lies in the pinned
hyperplane, which is affine — and it held on every independent pin in the sweep,
8 of 8.

**Dependent pins are where the coefficient is lost.** On the displayed instance
the maximal coefficient is exactly `1/2` before the pin, exactly `1/2` after an
independent pin, and exactly `0` after a dependent one — every positive
coefficient fails. Across 28 dependent pins in the sweep, 6 void the coefficient
outright and 6 strictly lower it.

The linear reformulation is what made all of this tractable, and it is the
pass's most useful incidental finding: containment of the homothet is **linear
in the reference at fixed coefficient**. Consequences — satisfiability now is a
linear program; the maximal coefficient is the boundary of a monotone predicate,
exact in closed form as `(M - r) / (M - m)` when one row binds and a verified
bracket otherwise; and the clipping adapter is a real construction rather than a
hope.

## WP-4 — the empirical channel

Request, scheduled execution, pin, and the pin's three downstream effects wired
to the existing interval computer, instrument resolution, and objection surface.

Two typed obstructions, both stated as disclosures rather than proofs. The
request key has **no field an outcome could occupy**, so the map from funding
intents to keys forgets direction and two funders intending opposite settlements
write the same key. And the executor's signature admits the procedure, the date
and the world — nothing else — so no path from book or purse to a pin value can
be written *in this implementation*. That is a fact about this construction; the
faithfulness axiom quantifies over every engine and is untouched.

**The adequacy inequality** is stated in general form: a per-query inequality
(admission plus upstream horizon plus service fits the deadline) and a
release-aware window inequality (work released in a window fits the capacity the
window supplies). Its earlier deadline-only form was wrong and is corrected
(`DEVIATIONS.md` 64). On the constructed channel, adequacy implies
earliest-deadline-first meets every deadline; the same channel with one deadline
tightened violates both inequalities and does miss one; and a capacity-only
instance is adequate query-by-query while jointly impossible. On a purely
logical docket the inequality has no upstream term and is satisfied with nothing
to check — coverage of nothing, recorded as such.

Conduct: the precommitted rule's stop date is invariant under replay against
opposite worlds; the blackout objection fires inside the window and not on a
stale position, an outside one, or another actor's; provenance per pin feeds a
common-source objection that fires on one purse and not on two. Both new
objection types are judged through the existing grammar verifier under declared
footprints, not by direct call.

## WP-5 — two engines

Disjoint declared jurisdictions, checked; overlaps and foreign owners caught.

**Redundancy never reaches the settled record.** Two thermometers disagreeing
about one world claim are two procedures, two report variables, two pins that
write-once cannot bring into conflict. The disagreement is real and surfaces
where the interface says it should: two endorsed bridge warrants pulling
opposite ways make the *book's* region infeasible, reported by the existing
sure-loss surface against the book. The pens are untouched.

**Breach is isolated by channel**, and the witness separates the two tolling
causes. Reporting one flag would let the tolling the rateless channel already
carries masquerade as a failure of isolation; separated, the logical channel is tolled
for its own reason and not by the empirical breach.

**The purse composes only inside its fences.** Each engine declares its own
limit, exposure is bounded by the fenced sum, and a transfer between provenances
fires the existing cross-subsidy objection while one inside a provenance does
not. The pooled control declares no fence, so nothing crosses.

---

## Prediction scores

**ρ1 — CONFIRMED, with one refinement.** The mapping is not an identity. The
bundle has no write-once formulation, and two of its conditions are strictly
stronger than any clause needs. The refinement is on the tolerance half: the
bundle is not simply missing a tolerance clause, it carries an error budget of a
*different kind* — a solver budget on quote selection, not a bound on how
incoherent prices may be. The bundle has no coherence tolerance and the
interface has no solver-error budget, so the parametric composite must carry the
latter as a hypothesis even with every engine clause discharged.

**ρ2 — CONFIRMED.** The ambient reading voids on the first exact pin, the
two-sentence witness exists and is displayed, the relative reading survives
independent pins (8 of 8 by transport), and a displayed dependent-pin case fails
— totally, from `1/2` to `0`, not merely by degradation.

**ρ3 — NOT CONFIRMED as stated; the shape is right.** The theorem goes through,
and the instance corollary carries exactly the three named conditionals as
predicted. But additional hypotheses *were* discovered: four bundle conditions
have no interface counterpart and must be carried explicitly. They are not
additional *engine* hypotheses — they are mechanism-side, which is why no clause
covers them — so the prediction is right about the clause list and wrong about
the hypothesis list. The theorem's antecedent has thirteen hypothesis objects,
not three.

**ρ4 — SPLIT.** The first half is confirmed: non-vacuity is exactly a
strict-separation check. The second half is not. The boundary on the displayed
book is a genuine crossover at `1/10`, where the interval is a proper
subinterval and the book is non-empty — distinct from the empty-book
degeneration catalogued in the corpus, which appears here at tolerance one as a
separate phenomenon. Both are exhibited, and the tests assert they are different.

**ρ5 — CONFIRMED.** Every conduct and multi-engine witness fires and every
control does not: the blackout objection with three controls, the common-source
objection with a two-purse control, the cross-subsidy crossing with a
within-provenance control and a pooled control, and the disagreement witness
with no pin conflict. No existing docket or grammar invariant was violated: no
pre-existing test file was edited and all 227 remain green.

One consequence is worth stating rather than leaving for a reader to find.
Registering two objection types moved the grammar's computed classification, as
the previous pass's addition did: twelve types now, ten footprint classes and
nine evidence classes, and the computed classification splits **all four**
declared legacy families rather than three. The two settlement types are what
split the last one — they read the settlement surface and supply no standard,
where the two calibration-family types both read the endorsement table as
standard. `GRAMMAR.md`, the `GR-J2` row and this report were updated together;
the claim's content is unchanged and its scope line now says twelve
(`DEVIATIONS.md` 63).

## Counts

| quantity | value |
|---|---|
| tests before | 227 |
| tests after | **388** (+161) |
| new source modules | 6 (`settlement_interface`, `coherence`, `core_geometry`, `parametric_composition`, `settlement_channel`, `two_engines`) |
| new test modules | 6 |
| new source lines | 3,935 |
| new ledger rows | 17 (`NL-SI-0` … `NL-SI-15`, plus the guard row `NL-SI-1B`) |
| new deviations entries | 8 (58–65) |
| new registry tables / objection types | 3 / 2 |
| full suite runtime | ~37 s |
| pinned digests verified | 70, unchanged |

Per package: WP-0 36, WP-1 23, WP-2 24, WP-3 21, WP-4 33, WP-5 24. All green,
no skips.

## Boundary contacts

Two work items touched a reserved boundary and stopped.

**The deduction budget.** The empirical channel's funding path is built and the
logical channel's is not. A settlement request may name a theorem-question in
the type, but nothing here makes a deductive process funding-responsive, because
that is the reserved clause. The request key is channel-neutral, so adopting a
budgeted process later requires no change to it.

**The coherence modulus.** WP-1 defines the quantity a modulus would have to
bound and makes conformance checkable, and the layering route lets the mechanism
operate without one. Whether any particular engine admits a computable schedule
tending to zero is untouched and remains open in both directions.

## What this does NOT show

- **The parametric composite consumes the checkable fragment plus a named
  hypothesis list — not the assumed residue.** It is a substitution over the
  corpus composite and inherits every hypothesis that composite inherits. It
  proves nothing the corpus did not, and it does not establish the composite
  guarantee: satisfying the interface is the *antecedent* of that conditional.
- **The instance corollary is not the witness theorem.** The pair it quantifies
  over is described by a reading audit and is constructed nowhere in this tree.
- **WP-3 is finite-instance evidence, not an asymptotic result.** The reported
  minimum is over a searched finite trajectory of displayed kernels. The
  persistence of a declared core minimum is exactly as open as it was; the
  per-date program narrows the question and does not answer it, because no
  per-date check bounds an infimum over time.
- **The typed obstructions are disclosures about this implementation.** A
  signature that cannot express a dependence is not a proof that no engine has
  one. The faithfulness axiom and the checker's soundness remain assumed, named,
  and unaudited — as the interface says they must be.
- **Nothing here touches the deduction-budget clause or the coherence modulus**,
  and no clause revision has been made to the interface document: the one
  restatement this work supports is recorded above as a proposal.
- **No incentive, behavioural, convergence, or learning claim is made
  anywhere.** Every result says what the record must show. Tariffs, subsidies
  and liabilities are accounted quantities, not motives.
- **The engines exhibited are trivial by design.** The reference engine and the
  lookup prover prove that the checkable fragment is jointly satisfiable, which
  is a statement about the fragment, not evidence that any interesting engine
  satisfies it.
