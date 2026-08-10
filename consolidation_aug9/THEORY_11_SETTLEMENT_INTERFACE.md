# Theory 11: the settlement interface

This part defines the interface a world-channel must meet before the mechanism
grants its writings operative force, and states what is known about whether any
engine meets it. It continues the numbering of the previous consolidation, whose
six parts remain authoritative for their own content; nothing there is restated
except where a result here modifies or repairs it, and each such place says so.

Every symbol used here is defined here.

## 0. Vocabulary, and one retirement

A **settlement engine** supplies exactly three things: **reports** — what it
writes into the settled record; **timing** — when it writes; and
**enforcement** — the weight standing behind what it writes. An earlier draft
called these the pen, the clock and the purse; that triple is retired, and the
section names below follow the plain terms.

The clause letters `J`, `C`, `P`, `T`, `F` are **frozen opaque identifiers**.
They are entrenched in the reading audit, in the correspondence table of
Theory 12, and in the verifier's predicate names, so they are kept as labels
while the prose carries the real names. This is the same fossil treatment the
transport identifiers received in the source tree. `GLOSSARY.md` maps each
letter to its subject.

Three further vocabulary items are canonical here and are recorded with their
history in `GLOSSARY.md`: **incoherence** for the quantity the tolerance clause
measures, **downside limit** for the worldwise loss guarantee — *bound* is
reserved for one-sided endorsement constraints and is not reused — and **core
minimum** for the certified enforcement coefficient, written `theta_min`.

## 1. The settled record

Fix a finite set of **worlds** `W` and a finite **language fragment**: a set of
sentences together with, for each, the worlds at which it is true. The
**indicator** of a sentence is its `0/1` vector over `W`. A **credal state** is
a probability assignment `p` over `W`; the probability of a sentence is the
inner product of its indicator with `p`.

A **procedure** `q` is declared with an **outcome space** `O_q` of at least two
values, a **channel** (logical or empirical), an **owner**, and — on the
empirical channel — a **horizon**. The **report variable** of procedure `q`
executed at date `t` is written `X(q,t)`; its identity carries which procedure
and when, so what settles is always what the procedure returned, never the
world-fact behind it.

A **settlement event** is a dated record event `(X(q,t), v)` with `v` in `O_q`.
From date `t` forward every feasible credal state satisfies `X(q,t) = v` with
probability one. A settlement event does three things downstream: it
**constrains** — the equality enters every region and interval, permanently; it
**pays** — instruments referencing the variable resolve at `v`; and it
**grounds** — it is citable as evidence without ever being the target of an
objection.

A settlement event is defined as much by its absences. It carries no basis tag,
no stake, no charge stream and no objection surface: it is the one record
citizen exempt from every column the answerability ledger tracks.
Incorrigibility here is not certainty; it is exemption from the answerability
economy.

**No claw-back.** {#NL-SI-P1} **Status: PROVED (single derivation).** A
settlement event is never reopened.

**Proof.** Suppose settlements could be reopened. Then an instrument that has
already resolved may resolve again with a different value, so the cumulative
transfer against a fixed holding is not determined by the record. An agent able
to trigger reopening therefore faces a payoff it can revisit, which is exactly
the structure the previous consolidation refutes for exposed content: a false
exposed constraint survives arbitrarily many tests when an outside source
replenishes every paid loss and only current locks are tracked. That refutation
is by a displayed witness there, and the repair adopted there is a limit on
cumulative net outflow, not a re-litigation of what was settled. Reopening
reinstates precisely the refuted structure, so it is excluded. `square`

## 2. The two polytopes

Two constraint sets are named separately throughout, and conflating them
misassigns liability.

The **coherence polytope** `K(W, S)` is the set of credal states satisfying the
simplex — coordinates nonnegative, total one — together with every settlement
equality in the settled record `S`. Nothing else. This is what an engine's
prices are obliged to be near.

The **docket polytope** `D(W, S, B)` adds the book `B`: each **endorsement** is
a one-sided constraint `c . p >= r` on the credal state. This is what the docket
computes intervals against.

The **credal interval** of a target over a constraint set is the exact rational
minimum and maximum of the target's probability over that set, attained at
vertices and computed by enumeration.

**Separation of respondents.** {#NL-SI-P2} **Status: NECESSITY WITNESS.** The
incoherence functional of §3 must be measured on the coherence polytope and not
on the docket polytope.

**Witness.** Take `W = {w1, w2, w3}` with `A` true at `{w1, w2}`. Let the book
endorse both `p(A) >= 3/4` and `-p(A) >= -1/4`. The docket polytope is empty:
no credal state satisfies both. Let the engine's displayed price be
`p(A) = 1/2`, which is realized by the credal state `(1/2, 0, 1/2)` in the
coherence polytope, so the engine's incoherence is exactly `0`.

Measured on the coherence polytope, the engine conforms and the empty docket
region is the book's own sure loss, chargeable to the book. Measured on the
docket polytope, the same instance would report an engine breach, and by the
layering of §5 the mechanism's clocks would toll for a failure the engine did
not commit — the opposite respondent and the opposite consequence. `square`

## 3. Incoherence

**Definition.** Let a **price assignment** give a rational value in `[0,1]` to
each sentence of a finite priced fragment. Its **incoherence** relative to a
settled record is

    inc(prices) = min over p in K(W,S) of max over priced s of
                  | <indicator(s), p> - price(s) | .

Prices are **`e`-coherent** exactly when their incoherence is at most `e`.

**The normalization.** The scale is not stipulated, and two facts fix it. Each
priced row is a sentence indicator, with `0/1` coefficients and an expectation
ranging over the whole unit interval, so a value of `1` means a displayed
sentence is priced at the opposite end of its entire attainable range. And the
certificate below carries total absolute mass at most one — which is *forced*,
being the tolerance column of the dual system, not a convention. A certificate
reporting excess `g` therefore reports it in the same units as a declared
schedule.

This matters more than it may appear. Without a fixed normalization the sentence
"a declared tolerance of one bounds the incoherence" is not weak but
**meaningless**: there is no scale on which one is large, and an engine could
satisfy any schedule by rescaling its own measure.

**Certificate.** A **normalized certificate** is a vector of signed weights
`w_s` on priced sentences with `sum |w_s| <= 1`, together with a rational `g`,
such that for every `p` in the coherence polytope

    sum_s w_s ( price(s) - <indicator(s), p> )  >=  g .

**The functional is computed by one linear program.** {#NL-SI-C1}
**Status: PROVED (single derivation).** The incoherence is an exact rational,
attained, and computed by minimizing one variable over a pointed polyhedron.

**Proof.** Introduce a variable `e` and impose, for each priced `s`, the two
rows `<indicator(s), p> + e >= price(s)` and `-<indicator(s), p> + e >=
-price(s)`, together with `e >= 0` and the rows of `K(W,S)`. A pair `(p, e)` is
feasible exactly when `p` is coherent and every priced deviation is at most `e`,
so minimizing `e` is the displayed minimum. The region is pointed: `p` is
confined to the simplex and `e` is bounded below, so its recession cone is the
ray in `e`, which contains no line. A linear objective bounded below on a
pointed polyhedron attains its minimum at a vertex, and vertices are solutions
of square subsystems, so enumeration over subsystems is exact and terminates.
`square`

**A certificate bounds the functional below.** {#NL-SI-C2}
**Status: PROVED (single derivation).** If `(w, g)` is a normalized certificate
then `inc(prices) >= g`.

**Proof.** Let `p` be any coherent state and write `d_s = price(s) -
<indicator(s), p>`. Then `g <= sum_s w_s d_s <= sum_s |w_s| |d_s| <=
(sum_s |w_s|) max_s |d_s| <= max_s |d_s|`, using `sum |w_s| <= 1`. So every
coherent state has some priced deviation at least `g`, and the minimum over
coherent states of the maximum deviation is at least `g`. `square`

**Zero exactly when realizable.** {#NL-SI-C3} **Status: PROVED (single
derivation).** `inc(prices) = 0` if and only if some coherent state reproduces
every displayed price exactly.

**Proof.** If some coherent `p` has `<indicator(s), p> = price(s)` for all
priced `s`, then `(p, 0)` is feasible in the program of `NL-SI-C1` and the
minimum, being nonnegative, is `0`. Conversely if the minimum is `0` it is
attained at a vertex `(p, 0)`, and the two rows per sentence then force
`<indicator(s), p> = price(s)` exactly. `square`

**Monotone under settlement.** {#NL-SI-C4} **Status: PROVED (single
derivation).** Adding a settlement equality, or any further constraint on the
coherence polytope, does not decrease the incoherence.

**Proof.** Adding a constraint replaces the coherence polytope by a subset. The
objective is unchanged, and a minimum over a subset is at least the minimum over
the set. `square`

**The displayed instance.** {#NL-SI-C5} **Status: MACHINE-CHECKED (stated
finite scope).** With `W = {w1,w2,w3}`, `A` true at `{w1,w2}`, `B` at
`{w2,w3}`, `C` at `{w2}`, no settled record, and prices `A = 9/10`, `B = 9/10`,
`C = 0`, the incoherence is exactly `4/15`, and the certificate
`w = (1/3, 1/3, -1/3)` has mass exactly `1` and excess exactly `4/15`.

**Derivation.** Write `a = p(A)`, `b = p(B)`, `c = p(C)`. Since `A` and `B`
overlap exactly at `w2` and `C` is `w2`, every credal state satisfies
`a + b - c = p1 + p2 + p2 + p3 - p2 = 1`. The prices demand `a + b - c = 9/5`.
Let `e` bound each deviation. Then `a >= 9/10 - e`, `b >= 9/10 - e` and
`c <= e`, so `1 = a + b - c >= 9/5 - 3e`, giving `e >= 4/15`. The value is
attained: `c = 4/15`, `a = b = 19/30`, that is `p = (11/30, 8/30, 11/30)`, which
is a credal state with each deviation exactly `4/15`. For the certificate, the
combination `1*(A) + 1*(B) - 1*(C)` is identically `1` on credal states, so with
weights scaled by `1/3` — total absolute mass exactly one — the guaranteed value
is `(1/3)(9/10) + (1/3)(9/10) - (1/3)(0) - (1/3)(1) = 3/5 - 1/3 = 4/15`. The
bound of `NL-SI-C2` is therefore attained, so the certificate is tight. `square`

## 4. The clauses

Each clause is one predicate of exactly one kind. **Checkable**: a computable
predicate over declared engine data and a finite record prefix, returning the
obstructions it found. **Declared**: a hypothesis object carrying its own
statement, holding exactly when a matching object is supplied. The split is the
honesty mechanism — an engine satisfying the interface has been checked *plus* a
printed list of what nobody checked.

### Reports

**(J1) Declared settleable class.** The engine declares its procedures, each
with outcome space, channel, and where applicable a horizon. Nothing outside the
induced family of report variables is settleable by this engine. *Checkable.*

**(J2) Write-once, owner-only.** Every report variable is settleable exactly
once and only by the engine owning its procedure. Cross-event conflict is
vacuous by construction: no variable has two writers or two events. Redundancy
is expected — two procedures bearing on one world claim are two variables — and
their disagreement lives constitutively in the answerable layer. *Checkable.*

**(J3) Transport under migration: bridge, never re-settle.** Settlements are
historical record and are never re-spoken in a new vocabulary; translated
content reaches the new ontology through migration cells in the answerable
layer. *Checkable over an era-stamped prefix.*

**Write-once holds under consistency, and only then.** {#NL-SI-J2}
**Status: PROVED-CONDITIONAL (conditions listed).** Let the engine's reports on
the logical channel be generated by a computable nested sequence of finite
sentence sets — stage sets increasing under inclusion, with the union written
`D_inf` — interpreted as the theorems of a declared theory. If the theory is
**consistent**, write-once holds. If it is inconsistent, some variable receives
two events with conflicting values.

**Proof.** Nesting gives that once a sentence enters a stage set it is in every
later one, so the first stage at which the process resolves a question is
unique, and the event written there is the only one. If the theory is
consistent, at most one of a sentence and its negation is ever emitted, so the
question `phi` receives one value. If it is inconsistent, both `phi` and its
negation eventually appear, and the variable for the question `phi` receives
both `proved` and `refuted`. Consistency is a hypothesis and not a guarantee: it
is not provable in the theory itself. `square`

**Breach handling is cost allocation, never satisfaction.** {#NL-SI-J2B}
**Status: PROVED (single derivation).** The double-event case of `NL-SI-J2` is
routed by §6 as a jurisdiction violation, and this routing does not make J2
satisfied.

**Proof.** J2 asserts that every variable is settleable exactly once. In the
inconsistent case a variable is settled twice, so the assertion is false of that
record, whatever the constitution then does. Routing assigns the cost of a false
assertion; it does not make it true. `square`

### Timing

**(C1) Completeness, split by channel.** On the logical channel, define the
engine's **decidable fragment**

    Dec(D) = { phi : the declared process eventually emits phi,
                     or eventually emits the negation of phi } .

This is **not** the union of what the process emits: writing `D_inf` for that
union, `Dec(D) = { phi : phi in D_inf or not-phi in D_inf }`. For a theory such
as first-order arithmetic, `Dec(D)` is a proper subset of the language, since a
sentence independent of the theory lies in neither `D_inf` nor its negation
image. Completeness is the requirement that `Dec(D)` contain the declared
logical jurisdiction, **with no rate promised**: the interface requires no
horizon function on this channel and downstream machinery must not assume one.
Satisfying it therefore imposes a *declaration discipline* on J1 — the declared
jurisdiction must lie inside the engine's own decidable fragment. *Declared: no
finite prefix decides an eventuality.*

On the empirical channel, completeness is **funding-responsive**: every report
variable in the declared observable class settles if its procedure is funded and
run, with a declared horizon per procedure. *Checkable in exactly that
conditional form.*

**(C2) Ripeness and tolling.** At admission, a query whose merits would require
settlement faster than a declared horizon is **unripe** — deferred without
liability. At runtime, settlement later than a declared horizon, and all
dependence on the rateless logical channel, **tolls** the affected refusal
clocks. *Checkable.*

**(C3) Adequacy.** The docket's schedules, capacity and deadlines must be
adequate relative to the declared horizons. The inequality is stated and proved
in Theory 12 §4, where the channel it constrains is constructed. *Checkable.*

### Enforcement

**(P1) Enforcement minimum, relative reading.** The engine certifies a core
minimum `theta_min > 0`, and the core condition is read **relative to the
post-settlement simplex**: writing `P` for the credal states consistent with the
settled record alone and `S` for the endorsed region inside it, the condition on
a reference `q` is

    q + theta ( P - q )  contained in  S .

*Checkable at each date, by §5.* Persistence of the minimum is a separate
declared clause.

**(P2) Downside establishment.** The engine guarantees a worldwise **downside
limit** `-B` against the book's holdings, and declares the means: refusal where
the engine may refuse trades, bounded aggregate participant budgets where it may
not. *Checkable.*

**(P3) Finite gating.** Engine-facing instruments are gated: finitely many live
per date, admitted under a fair queue with finite overtaking. *Checkable.*

**(P4) Declared certificate type.** The engine names the soundness guarantee its
pricing process carries, and the composite's empirical conjunct is stated
relative to the declared type. *Naming is checkable; the named type's semantics
holding is declared.*

### Tolerance

**(T1) Tolerance schedule, with the adopted functional.** Engines whose prices
are only approximately coherent at finite times declare a schedule `e_t`, and
the docket runs the robust interval, merits certificate and sure-loss objection
against it. The quantity `e_t` bounds is the **incoherence** of §3; conformance
is checked by the normalized certificate. An exactly coherent engine declares
`e_t = 0` and the robust forms reduce to the exact ones. *Checkable.*

**Non-vacuity.** A declared tolerance is **working** at a date exactly when the
induced robust interval still strictly separates for the displayed book — that
is, when some merits direction survives the relaxation. Working is a property of
the declaration together with the book, not of the declaration alone.

**(T2) Certification layering.** The engine certifies its own tolerances; breach of
a certified tolerance is the engine's and tolls. The book may voluntarily declare
tighter working tolerances; breach of a self-declared tighter bound is the
book's, and chargeable. *Checkable.*

### Conduct

**(F1) Request-keyed subsidy.** Subsidies attach to a **request key**: target,
procedure, funder, timing. A key names a question, never an outcome.
**(F2) Stopping neutrality.** The funder's stopping policy creates no
directional bias. Two witnesses are named — a precommitted rule, or an
anytime-valid certificate — and *which are available is engine-relative*.
**(F3) Probe blackout.** The funder takes no fresh position on the target
between funding and settlement.
**(F4) Funder provenance.** Funding profiles are recorded per settlement event.
*All four checkable; F3 and F4 are new objection types, discharged in Theory 12.*

### The residues

On the empirical channel the assumed residue is **procedural faithfulness**:
conditional on the declared procedure, its declared inputs, and the realized
world, a settlement's value has no further dependence on anything — in
particular none on the book's states or any funding profile. This permits
performativity, since an agent changing the world changes what the procedure
faithfully reports; what it excludes is any extra path from book or purse to the
value. On the logical channel settlements are **proof-carrying** — each ships a
derivation certificate checkable by a fixed proof checker — so derivation is
auditable and what remains assumed is the checker's soundness.

## 5. The core condition under settlement

Write `P` for the post-settlement simplex — the credal states consistent with
the settled record alone — and `S` for the endorsed region inside it. Write
`P_amb` for the whole simplex over `W`.

**The ambient reading voids on the first settlement.** {#NL-SI-A1}
**Status: NECESSITY WITNESS.** Read against `P_amb`, the core condition fails
for **every** positive coefficient as soon as one non-trivial settlement is
recorded.

**Witness and argument.** Take `W = {w1, w2}` with `A` true at `{w1}` and `B` at
`{w2}`, no endorsements, and the settlement `A = 1/2`. The endorsed region is
then the single state `(1/2, 1/2)`. For any reference `q` in it and any
`theta > 0`, the homothet `q + theta(P_amb - q)` contains the two distinct
points `q + theta((1,0) - q)` and `q + theta((0,1) - q)`, which differ in their
first coordinate by exactly `theta`. A set containing two distinct points is not
contained in a singleton, so containment fails for every `theta > 0`.

The failure is not an artifact of the region collapsing to a point. Take
`W = {w1,w2,w3}` with `A` true at `{w1,w2}` and the settlement `A = 1/2`. The
endorsed region is the segment `{ p : p1 + p2 = 1/2 }`, one-dimensional and not a
point, and for the reference `(1/4, 1/4, 1/2)` and any `theta > 0` the point
`q + theta((1,0,0) - q)` has first-plus-second coordinate `1/2 + theta/2`, which
leaves the segment. Generally: a settlement is an equality, so the endorsed
region lies in a hyperplane, while a positive homothet of the ambient simplex
spans the simplex's own affine hull; the second is not contained in the first.
This is the necessity witness for the relative reading. `square`

**The relative core is a linear condition on the reference.** {#NL-SI-A2}
**Status: PROVED (single derivation).** For fixed `theta` in `(0,1]`, the set of
references satisfying `q + theta(P - q) subset S` is a polytope, cut out by one
linear inequality per endorsed row.

**Proof.** `P` is a polytope, so it is the convex hull of its finitely many
vertices, and the homothet is the convex hull of the shrunk vertices. `S` is an
intersection of half-spaces, hence convex, so it contains the homothet exactly
when it contains each shrunk vertex. For an endorsed row `c . x >= r` and a
vertex `v`, the shrunk vertex condition reads

    (1 - theta) <c, q> + theta <c, v>  >=  r ,

which is linear in `q`. Minimizing the left side over vertices replaces the
whole family by one row per endorsement, namely
`(1 - theta) <c, q> >= r - theta m_c` with `m_c = min over vertices of <c, v>`.
Intersecting these with `P` gives the polytope. `square`

**Corollary (the clipping adapter).** {#NL-SI-A3} **Status: PROVED (single
derivation).** Whether a declared core minimum is satisfiable *at a date* is
decided by one linear program, and emptiness is a detected condition with a
declared consequence.

**Proof.** By `NL-SI-A2` the admissible references form a polytope described by
finitely many rational rows, and nonemptiness of such a polytope is decided by
vertex enumeration. The adapter restricts the reference to that polytope where
it is nonempty; where it is empty it declares the breach consequence
**quarantine of operative force** rather than proceeding on a coefficient it
cannot support, and rather than silently lowering the declared minimum. `square`

**What the per-date program does not decide.** {#NL-SI-A4}
**Status: PROVED (single derivation).** No finite family of per-date checks
bounds the infimum over dates of the maximal satisfiable coefficient.

**Proof.** A per-date check is a statement about one settled record. The infimum
over an unbounded sequence of records is not determined by any finite subfamily
of them: extend any finite trajectory by a settlement whose endorsed region
forces the coefficient lower, which `NL-SI-A6` exhibits is possible. Hence
persistence is not entailed and remains a declared hypothesis. `square`

**Single-row closed form.** {#NL-SI-A5} **Status: PROVED (single derivation).**
If `S = P` cut by one row `c . x >= r`, with `m = min_P <c,.>` and
`M = max_P <c,.>` and `m <= r <= M`, the maximal satisfiable coefficient is
exactly `(M - r) / (M - m)`.

**Proof.** By `NL-SI-A2` the condition at reference `q` is
`(1 - theta) <c,q> + theta m >= r`. Taking `q` at a maximizer gives
`(1 - theta) M + theta m >= r`, that is `theta (M - m) <= M - r`, so
`theta <= (M - r)/(M - m)`, and that value is achieved there. No reference does
better, since the condition forces `(1 - theta)<c,q> + theta m >= r` with
`<c,q> <= M`. When `M = m` the row is constant on `P` and any `theta` works;
when `M < r` no reference satisfies the row at all. `square`

**Consequently** the per-row minimum of `(M - r)/(M - m)` is an exact upper
bound in the multi-row case, since the joint condition implies each single-row
condition; it need not be attained when two rows pull the reference apart.

**Transport across a confirmed settlement.** {#NL-SI-A6}
**Status: PROVED (single derivation).** Suppose the relative core condition
holds at reference `q` with coefficient `theta`, and a new settlement `(s, v)`
is **confirmed by `q`**, meaning `<indicator(s), q> = v`. Then the same `q` and
the same `theta` satisfy the relative core condition after the settlement.

**Proof.** Write `H` for the hyperplane `<indicator(s), x> = v`. The
post-settlement simplex is `P' = P ∩ H` and the endorsed region is `S' = S ∩ H`.
Let `x` be in `P'`. Then `x` is in `P`, so `q + theta(x - q)` is in `S` by
hypothesis. Also `q` is in `H` by confirmation and `x` is in `H` by
construction, and `H` is affine, so the whole segment between them — in
particular `q + theta(x - q)` — is in `H`. Hence the point is in `S ∩ H = S'`,
which is the post-settlement condition. `square`

**Dependent settlements are where the coefficient is lost.** {#NL-SI-A7}
**Status: MACHINE-CHECKED (stated finite scope).** A settlement the incumbent
reference contradicts can destroy a core that a confirmed settlement preserves.

**Displayed instance.** `W = {w1,w2,w3}`, sentences `A`, `B`, `C` true at the
respective single worlds, and one endorsement `p1 >= 1/2`. Before any
settlement, `NL-SI-A5` gives the maximal coefficient `(1 - 1/2)/(1 - 0) = 1/2`,
attained at `q = (1,0,0)`. Settling `B = 0` is confirmed by that reference and
leaves the maximal coefficient at `1/2`. Settling `B = 1/2` is not confirmed by
it; afterwards the post-settlement simplex is the segment from `(0,1/2,1/2)` to
`(1/2,1/2,0)`, on which the row `p1` ranges over `[0, 1/2]`, so `M = r = 1/2`
and the closed form gives `0`: **every positive coefficient fails**.

Over the exact-rational sweep of four endorsed rows against nine candidate
settlements, all `8` confirmed settlements transport, and of the `28` dependent
ones `6` void the coefficient outright and `6` strictly lower it. This is
finite-instance evidence over displayed instances and is not an asymptotic
claim. `square`

## 6. Breach

Detectable breaches are missed certified horizons, tolerance violations beyond
the declared schedule witnessed by a normalized certificate, jurisdiction
violations — a settlement outside the declared class, or a second settlement on
one variable — and gating violations. A breach is an **authorless cost**: the
world cannot be charged. So the clause is cost allocation, in three steps.
**Toll**: the clocks the breach touches pause, so substrate failure never
converts into unearned book liability. **Quarantine**: the channel in breach is
frozen; unaffected channels run on. **Escalate**: persistent breach is
constitutional grounds for era change. Per `NL-SI-J2B`, none of this is
satisfaction of the clause breached.

This stack and the layering of T2 are declared constitutional content rather
than mechanism structure, so revising either later is a lawful in-system act.

## 7. The interface as one object, and its witness

**The checkable fragment is jointly satisfiable.** {#NL-SI-W1}
**Status: NECESSITY WITNESS.** There is an engine satisfying every checkable
clause on a displayed finite record prefix.

**Witness.** The **reference engine**: two declared procedures, one empirical
with outcome space `{cold, warm}` and horizon `2`, one logical with outcome
space `{proved, refuted}`; a table of what it reports; an exact tolerance
schedule; refusal as its declared means with downside limit `0`; core minimum
`1/4`; gating capacity `2`; overtaking bound `4`. On the displayed prefix — one
funded request executed at its precommitted date and settled, one logical
settlement shipping a derivation, two admitted queries with the logical one
tolled, and one priced state whose prices are exactly realizable — all seventeen
checkable predicates return no obstruction, and the three declared predicates
return failure until hypothesis objects are supplied. Non-vacuity is discharged
by the construction, not by a stand-in. `square`

**The audit outcome, as a result-class of its own.** {#NL-SI-SIM}
**Status: PROVED-CONDITIONAL (conditions listed).** The following is the outcome
of a **reading audit** of one candidate engine against this interface, and is
labelled as such: it is not a machine-checked result and not a proof from these
definitions. It is recorded because it is the only evidence about a non-trivial
engine that exists.

Let the candidate be the **pair** consisting of a declared deductive process
`D`, supplying reports and timing, and a market `P` over it satisfying that
framework's non-exploitation criterion, supplying enforcement, tolerance and the
certificate type. The pair is genuinely two objects straddling the boundary:
making the market the writer would key settlements to prices reaching one, which
nothing guarantees at any finite time; making `D` the whole engine leaves the
enforcement and tolerance clauses with no referent.

Under that split the pair inhabits

    SI-minus = { J1, J3, C1, C2, C3, P2, P3, P4, T2,
                 F2-via-precommitment, deduction-requirement (i) }

with C3 vacuous on the logical channel — there are no upstream horizons there
for an adequacy inequality to be adequate to, so the work is carried entirely by
C2's tolling — and F2 discharged by the precommitted witness only, since a
guarantee that is global over an entire price sequence issues no per-request
certificate for an anytime-valid witness to instantiate.

Two clauses sit **outside** SI-minus as named conditionals, because a
conditional inhabitation is not an inhabitation: **J2**, conditional on the
consistency of the declared theory per `NL-SI-J2`; and **P1**, conditional on
the persistence question of `NL-SI-A4`. Outside SI-minus entirely: **T1**, whose
status is the open problem below; the proof-carrying requirement, which needs
the modification below; and deduction-requirements (ii) and (iii).

**Delta list.** Four conditions, with classifications.

| id | statement | class | cost |
|---|---|---|---|
| D1 | a declared core minimum that remains satisfiable under the relative reading as the settled record grows | **open sub-problem** | unknown; the per-date program of `NL-SI-A3` decides a date, and `NL-SI-A4` shows it decides no infimum |
| D2 | instantiate the process as a proof enumerator emitting sentence-and-derivation pairs, with the stage sets the first projection | **modification**, negligible | near nil: concrete processes already compute the derivation and discard it, and the market reads only the projection |
| D3 | either a computable schedule tending to zero with prices provably conforming at every finite date, or the weakening to eventually-coherent-rateless with quarantine-on-detected-excess | (a) **modification**, existence open; (b) **weakening** | (b) costs the merits certificate its a-priori standing |
| D4 | funding-responsive deduction: a budget-indexed family of processes with the criterion restated relative to the realized process | **modification**, substantial | reserved; not costed |

D1 and D3 are the two that carry weight. D4 has **two inequivalent versions**
and this interface chooses between them nowhere: *acceleration*, where the
process is fixed and a budget buys progress along it by wall-clock, and
*attention*, where the budget selects what the process works on, making the
stream endogenous to the funder. Only the second makes the plausible-world set
funder-dependent.

Sufficiency, stated with its full antecedent: D1, D2 and D3 **together with
consistency of the declared theory** are jointly sufficient for the whole
interface excluding the deduction-budget clause, whose requirements (ii) and
(iii) additionally need D4. Consistency must be named here precisely because J2
sits outside SI-minus; with J2 inside the set it would ride along as a
qualifying remark and go missing from the sufficiency statement. `square`

**Tolerance: soundness and usefulness come apart.** {#NL-SI-T1}
**Status: PROVED (single derivation).** T1 as stated admits vacuous
satisfaction, and non-vacuity is a separate requirement.

**Proof.** Prices lie in `[0,1]`, so every deviation is at most one and the
incoherence is at most one; an engine declaring the schedule identically one
therefore never breaches. But at that tolerance every relaxable endorsement row
has its right-hand side reduced by its full coefficient magnitude, so the robust
region contains every credal state and the robust interval is `[0,1]`. No merits
direction clears any threshold in `(0,1)`, so no merits certificate ever issues.
Hence the declaration an engine can always honour certifies nothing, and
soundness and usefulness are not the same requirement. `square`

**The boundary is a genuine crossover.** {#NL-SI-T2} **Status: MACHINE-CHECKED
(stated finite scope).** On the displayed two-sentence book — `W` and the
language of `NL-SI-C5`, endorsements `p(A) >= 3/5` and `p(B) >= 4/5`, threshold
`1/2`, target `A` — the merits certificate clears exactly while the declared
tolerance is at most `1/10`.

**Derivation.** Relaxing `p(A) >= 3/5` by `e` gives `p(A) >= 3/5 - e`, and the
robust lower end of `A` is exactly that, since the remaining rows do not bind
below. It clears the threshold exactly when `3/5 - e >= 1/2`, that is `e <=
1/10`. At the boundary the interval is `[1/2, 1]`, a proper subinterval of the
unit interval with the book non-empty, so this crossover is distinct from the
degeneration of `NL-SI-T1`, which occurs at tolerance one. Both are exhibited
and they are not the same phenomenon. `square`

**The layering supplies a working tolerance without an engine certifying one.**
{#NL-SI-T3} **Status: PROVED (single derivation).** Under T2 the mechanism can
operate on a working tolerance even when the engine's only sound declaration is
the vacuous one.

**Proof.** Let the engine certify the schedule identically one, which by
`NL-SI-T1` it can always honour. Let the book voluntarily declare a tighter
tolerance `e` that is working for the displayed book, which by `NL-SI-T2` exists
whenever some tolerance is working. By T2, breach of the book's self-declared
bound is the book's and is chargeable, while the engine's certified tolerance
is unbreached. So the docket runs the robust forms at `e`, merits certificates
issue, and the epistemic gap is carried as a priced liability rather than
assumed away. This prices the open problem; it does not close it. `square`

**Attribution is total and exclusive.** {#NL-SI-T4} **Status: PROVED (single
derivation).** Given a certified tolerance `E` and an optional book-declared
`b <= E`, every realized incoherence falls in exactly one of three cases:
above `E`, the engine's — tolled, not chargeable; in `(b, E]`, the book's —
chargeable, not tolled; at most `b` (or at most `E` when no `b` is declared),
no breach.

**Proof.** The three cases partition the nonnegative reals given `b <= E`, and
the assignments are as stated by T2's text: a certified tolerance's breach is the
engine's and substrate failure never converts into unearned book liability; a
self-declared tighter bound's breach is the book's, which assumed the risk.
Requiring `b <= E` is what makes the middle interval well defined; a book
declaration looser than the engine's certification is refused as malformed.
`square`

## 8. What this part does not establish

The interface is a definition and the reading audit is a reading. `NL-SI-SIM` is
labelled a reading audit in the ledger and in `VERIFICATION.md`; producing
SI-minus is not proving that any engine inhabits it, and the witness theorem for
the candidate pair remains to be proved. Nothing here constructs the pair. The
persistence question `D1` and the modulus question `D3(a)` are open, the latter
in both directions. The deduction-budget clause's formal content is deliberately
absent, and is reserved.
