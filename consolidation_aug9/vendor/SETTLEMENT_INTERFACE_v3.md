# THE SETTLEMENT INTERFACE
*(internal draft 3)*

*Supersedes internal draft 2.1, applying the corrections of the §10 witness
audit. Register: project-internal architecting document; a consolidation pass
will later freeze the B-track state, and any external version comes after that.
It is written **self-contained** as practice for that version: every corpus
result cited carries its content in the sentence that cites it, so no reader is
sent to another tree to learn what a claim identifier means.*

*This document defines the interface parameter of the composite guarantee: the
guarantee is stated over ANY settlement engine satisfying the settlement
interface, with specific engines entering only as witnesses (§10). It is the
whole-system criterion question approached from the engineering side, and should
be read with the target-guarantee one-pager (E3), which STATES the guarantee
this document DEFINES the terms of.*

*This is a revision pass, not a redesign. No clause is added and no design
question is reopened. Items that appeared to need redesign are listed in
`SI_V3_CHANGELOG.md` under "flagged, not fixed"; §9 is untouched in both content
and framing.*

---

## 0. The object and the governing principle

A **settlement engine** is the mechanism's world-channel. It supplies exactly
three things, and nothing else:

- a **pen** — it writes *pins* into the settled record (§1);
- a **clock** — the timing of its writing (§3);
- a **purse** — the enforcement weight standing behind what it writes (§4).

The boundary this document draws, in one sentence: **the world is not
answerable to the learner.** The learner can challenge a procedure's
reliability, the bridge from a report to a world claim, its own
interpretation, its warrants, and its decisions — but at some point there is
just: *this is what the channel returned.* Settlement is the **only
unanswerable speech act** in the system: every other record citizen enters
staked, challengeable, chargeable, or revisable; a pin enters exempt.
Incorrigibility is not certainty; it is *exemption from the answerability
economy*. The governing design principle is therefore:

> **Minimize the unanswerable.** Whatever the exempt voice does not strictly
> need to say is said in the answerable layer instead, through warrants,
> where every piece of the mechanism applies.

**Auditability by channel.** The clock is fully auditable — a missed horizon is
record arithmetic. The purse is certifiable — posted budgets verify like
collateral. The pen's conformance to its declared tolerance is auditable *given
a fixed measure of incoherence*, by a Farkas check; the audit showed that the
measure is not fixed by draft 2.1 and that conformance is therefore not yet a
meaningful test, which is the subject of the T1 revision in §5. And the pen's
remaining semantics is assumed — the assumed residue *differs by channel* and is
stated exactly in §8.

**Clause levels.** Each clause binds at one of three levels:
**[E] engine-intrinsic** — a property of the settlement engine itself;
**[M] mechanism-compatibility** — what the leverage mechanism requires in
order to grant an engine's pins operative force: an interface *to this
mechanism*, not an abstract theory of world-channels;
**[P] engine-facing conduct protocol** — conditions on the surrounding
institution and funders, not on the engine.
Assignment: J1 [E] · J2 [E] · J3 [M] · C1 [E] · C2 [M] · C3 [M] ·
P1 [M] · P2 [M] · P3 [M] · P4 [E] · T1 [E] · T2 [E/M] · F1 [P] ·
F2 [P, with an engine-side certificate hook] · F3 [P] · F4 [P] ·
§8 [E, axioms] · §9 [E].

## 1. Pins

A **pin** is a dated record event of type

    (X_{p,t}, v)   with   v ∈ O_p,

where **X_{p,t} is the report variable** of declared procedure p executed at
date t, and O_p is p's declared outcome space. The variable's identity
carries the report content — *which procedure, when* — so that, per the
reports-only jurisdiction, what settles is always "what the procedure
returned," never the world-fact behind it. World-facts are reached from
report variables through **bridging warrants** (endorsed, defeasible,
undercuttable when a procedure was miscalibrated): the reliability of every
procedure is answerable content, while the pin itself is not.

Pinning fixes the variable's whole propositional family at once: from date t
forward, every feasible credal state satisfies μ(X_{p,t} = v) = 1 and
μ(X_{p,t} = v′) = 0 for all v′ ≠ v. A pin does exactly three things
downstream:

1. **Constrains** — the equalities above enter every region, interval,
   merits certificate, and leverage computation, permanently.
2. **Pays** — world-mode instruments referencing X_{p,t} resolve at v. The
   pin executes wealth transfers, which is why pins are never clawed back.
   Reopening a settlement would recreate the exploitation surface the corpus
   already refuted: a false exposed bound survives arbitrarily many tests when
   an outside source replenishes every paid loss and the accounting tracks only
   current locks, and the repair is a cap on cumulative net outflow, not a
   re-litigation of what was settled.
3. **Grounds** — a pin is citable as evidence in correspondence-family
   objections without ever being the target of one.

A pin is defined as much by its absences: **no basis tag, no stake, no
charge stream, no objection surface** — the one record citizen exempt from
every column the answerability ledger tracks. For logical pins, see §8: they
additionally carry a proof certificate.

## 2. Jurisdiction clauses

**(J1) Declared settleable class.** The engine declares, as public record,
the procedures it owns, each with its outcome space, channel (logical or
empirical), and — where applicable (C1) — horizon. The settleable class is
the induced family of report variables; nothing outside it is pinnable by
this engine.

**(J2) Write-once, owner-only.** Every report variable is pinnable exactly
once, and only by the engine owning its procedure. That is the entire
exclusivity clause, and it makes cross-pin conflict **vacuous by
construction**: no variable has two pinners or two pins. Redundancy is
welcome and expected — thermometer A and thermometer B are distinct
procedures, hence distinct report variables, both bearing on one answerable
world claim through their bridges — and their disagreement lives
*constitutively* in the answerable layer (bridge warrants and reliability
content), never in the settled record. The accounting for several engines at
once is carried by machinery the corpus already has: subsidies are keyed by
the provenance class the token gate already represents, rather than by program
index, and a misdeclared-provenance objection is filed when two indices claim
distinct subsidy classes that the public ancestry check places in one.

> **Inhabitation is conditional on consistency, for deductive engines.**
> Write-once holds for a deductive pen *because* its process is nested — once a
> sentence enters the enumeration it is in every later stage, so the first entry
> is the unique pin. If the declared theory is **inconsistent**, both a sentence
> and its negation eventually enter, and the same report variable receives two
> pins with conflicting values. Nothing in the standard notion of a deductive
> process excludes this, and worlds are not required to be consistent.
>
> So the honest statement is a conditional: **consistency of the declared
> theory ⇒ write-once**; inconsistency produces a double pin, which is a
> jurisdiction violation under §7 and is routed to the breach stack. Consistency
> is a hypothesis, not a guarantee — it is not provable in the theory itself —
> and the composite must name it rather than absorb it. Note that this
> conditional is *not* satisfaction of J2 by other means: see the principle
> stated in §7.

**(J3) Migration transport: bridge, never re-settle.** Under ontology
migration, pins are historical record and are never re-spoken in the new
vocabulary. Translated content reaches the new ontology through migration
cells in the answerable layer. Re-settlement would extend the unanswerable
voice into translation, violating the governing principle. Two existing results
carry this without modification: the administrative-continuity result, under
which the only permitted edit between certified migrations is a declared grant
of authorization identifiers, so a re-settlement in between is structurally
impossible; and the migration transport result's requirement that outstanding
meaning arrive exactly on the common carrier or receive an explicit legacy
disposition, never a silent substitution.

## 3. Clock clauses

**(C1) Completeness, split by channel.**

- *Logical channel.* Define the interface's settleable logical class
  operationally as the **D-decidable fragment** of the declared process:

      Dec(D) = { φ : D eventually proves φ, or D eventually proves ¬φ }.

  This is **not** the union of what the process proves. Writing D_∞ for that
  union — the set of sentences the process ever emits — the two are related by

      Dec(D) = { φ : φ ∈ D_∞ or ¬φ ∈ D_∞ },

  and Dec(D) is in general a **proper subset of the language**: for a theory
  such as Peano arithmetic, Gödel sentences lie in neither D_∞ nor its negation
  image, so they are never decided and are outside the fragment. Draft 2.1
  conflated the two sets and displayed an incorrect inclusion between them; the
  corrected reading is the one above.

  The completeness clause is that Dec(D) contains the declared logical
  jurisdiction — every sentence the engine claims for deduction is eventually
  settled — **with no rate promised**: the interface requires no horizon
  function for the logical channel and downstream machinery must not assume
  one. (Completeness is relative to the declared process; nothing here claims
  settlement of mathematical truth as such.) The clause is therefore satisfiable
  only under a **declaration discipline**: the engine must declare a
  jurisdiction lying inside its own decidable fragment. That is a real
  obligation on J1's declaration, not a formality.

- *Empirical channel:* **funding-responsive completeness** over the declared
  observable class — every report variable in the class settles *if its
  procedure is funded and run*, with a declared horizon per procedure.
  Universal unconditional observation is not a property any engine can
  honestly promise; experiments, unlike proofs, have schedules.

*Non-triviality note.* This interface constrains faithfulness and
completeness **relative to the declared jurisdiction**; the substantive
adequacy of the jurisdiction itself is deliberately not an interface
clause — it is a requirement of the composite system. It is, however, not
merely deferred: a book whose structural exposure outruns the declared
settleable class accumulates permanently-unripe queries and forced default
load, so jurisdictional inadequacy is *visible* in the mechanism's own
diagnostics through the time-and-pendency channel, even though it is never
certified against.

**(C2) Ripeness and tolling.** At admission: a query whose merits would
require settlement faster than a declared horizon is **unripe** — deferred
without liability. At runtime: settlement arriving later than its declared
horizon, and all dependence on the rateless logical channel, **tolls** the
affected refusal clocks. Queries hanging on deep unsettled theorems are
admitted and toll indefinitely; never-settling exposed content is
permanently unripe. Neither state accrues unearned book liability.

The clock this subtracts from already exists: refusal liability is derived as
elapsed time against a frozen tariff from a declared evaluation horizon, so
tolling is subtraction on a quantity the record already carries, and a snapshot
evaluation with no elapsed time carries no charge at all. Dates in arrears are
bounded by accumulated liability over the tariff, and "permanently unripe" is
the state of a query never admitted — which is precisely what admission control
exists to bound, as the necessity witness for admission shows by flooding an
unadmitted stream.

**(C3) Adequacy.** The docket's schedules, admission capacity, and deadline
structure must be adequate relative to the declared horizons: an inequality
relating downstream deadlines to upstream horizons, stated per instance and
checkable.

This generalizes a failure the corpus already displays and repairs. The failure:
without an adequacy condition, the bare terminal learning bridge is **false** —
a true bound can be suspended at effective age two purely because resource
competition prevents timely service, which is a displayed counterexample, not a
worry. The repair: the relativized bridge holds once **operational adequacy** is
assumed, and operational adequacy is exactly a capacity-against-latency
condition — capped stake, the token envelope, work-conserving service, and a
latency/capacity comparison sufficient to admit and service the required tests.
The same failure appears downstream as the service-inadequacy witness, in which
response latency exceeds the available service window and a correct target is
suspended for want of service. C3 is that condition, restated with the
*engine's declared horizons* as the upstream term.

*Observability remark.* The engine's world-faithfulness is assumed (§8); its
**speed is fully auditable** — missed horizons are arithmetic, and engine
slowness surfaces downstream as forced default load in the book's own
diagnostics. Substrate quality leaks into the mechanism's metrics through
exactly one channel: time.

## 4. Purse clauses [mechanism-compatibility]

*P1–P3 are compatibility conditions imposed by the leverage mechanism — see
the clause-level legend — not intrinsic properties of settlement engines. A
conformal predictor possesses no "conviction coefficient," nor need it; the core
coefficient, the downside floor, and the gating are what this mechanism demands
before an engine's pins are granted operative force.*

**(P1) Enforcement floor, relative reading.** The engine certifies a core
coefficient θ > 0 — a fixed θ, or a floor θ_min for a varying core — and the
core condition is read **relative to the post-settlement feasible simplex**:
writing P for the set of assignments consistent with the pins alone and S for
the endorsed region inside it, the condition is

    q + θ(P − q) ⊆ S.

The relative reading is not a refinement of taste. Under the **ambient**
reading, with P the whole simplex over the language, the clause is
*unsatisfiable* the moment anything is settled: a pin is an equality, so S lies
inside a hyperplane, while the homothet of the ambient simplex retains the
simplex's own dimension, and containment fails for **every** positive θ. A
two-sentence witness displays this, and it is not an artifact of a region
collapsing to a point — a three-world instance whose post-pin region is still a
segment fails the same way. An interface that kept the ambient reading would
have an antecedent nothing could inhabit once a single pin landed.

The operative-force cap is void under θ_t → 0; an engine whose conviction
decays delivers force that evaporates. The floor is a certified, verifiable
commitment, and under the relative reading it is verifiable in a strong sense:
containment of the homothet is **linear in q at fixed θ**, so whether a declared
θ_min is satisfiable *at a date* is a linear program over the admissible-
reference region. Where that region is non-empty the reference is clipped into
it; where it is empty, the condition is a detected breach with the declared
consequence **quarantine of operative force**, handled by §7. What the per-date
program does **not** decide is persistence — that θ_min keeps being satisfiable
as settlement contracts the region — and no per-date check bounds an infimum
over time. Persistence is the open residue, logged as Δ₁ in §10.

**(P2) Downside establishment.** The engine guarantees a worldwise downside
floor −B against the book's holdings. The *means* are engine-specific —
market refusal where the engine may refuse trades; bounded aggregate trader
budgets where it may not — but the abstract requirement is uniform, and the
establishing means must be declared.

**(P3) Finite gating.** Engine-facing instruments are gated: finitely many
live per date, admitted under a fair (finite-overtaking) queue. The prototype in
the corpus is the uniform policy's transition cycle, which fills freed world
slots first-in-first-out, admits eligible challenges in date-major order, and
selects the least unresolved objection with exposed inconsistency first; a
token-envelope queue result supplies the cap, and finite overtaking — no
admitted item deferred forever — is a hypothesis of the uniform finite-mechanism
construction. This is the universality-to-finiteness adapter, reconciling
engines with unbounded instrument spaces against the solvency-load-bearing
key-finiteness of the mechanism.

**(P4) Declared certificate type.** The engine names the soundness guarantee
its belief/pricing process carries — market non-exploitation, minimax
regret, Ville-style validity, conformal coverage, or another declared type —
and the composite guarantee's empirical conjunct is stated relative to the
declared type. The interface does not hard-code trader vocabulary.
*Formalization target:* an abstract relation **Cert_e(H, C)** — "under
engine e's declared semantics, certificate C establishes its advertised
guarantee on history H" — so the composite theorem is parameterized by the
certificate type's semantics, not by its name.

## 5. Tolerance clauses

**(T1) ε-schedule.** Engines whose price/belief states are only
approximately coherent at finite times declare a tolerance schedule ε_t.
Downstream, the docket runs the ε-robust interval, merits certificate, and
sure-loss objection against the declared schedule; an exactly coherent
engine declares ε_t ≡ 0 and the robust forms reduce to the exact ones.

> **(T1.a) The clause as written admits vacuous satisfaction.** Prices lie in
> ℚ ∩ [0,1], so any coherence defect is bounded by a constant, and an engine may
> honestly declare ε_t ≡ 1 and never breach. But at ε ≡ 1 the ε-robust interval
> is [0,1] at every date, so no merits certificate ever clears a threshold — the
> computed interval degenerates exactly as in the empty-book case, where a target
> with no endorsements and no settled premise bearing on it recovers the whole
> unit interval — and the ε-robust sure-loss objection never fires. Soundness and
> usefulness come apart: the declaration an engine can always honour is the one
> that certifies nothing.
>
> Therefore T1 additionally requires **non-vacuity**:
>
> > A declared tolerance is **working** at a date iff the induced ε-robust
> > interval can strictly separate for some nonempty book — that is, iff some
> > merits direction survives the relaxation at that tolerance.
>
> Working is a property of the declaration *together with* the displayed book,
> not of the declaration alone, and it is checkable at each date.
>
> **A definition this document owes.** The exact finite-time defect functional —
> what quantity ε_t is a bound *on* — is not fixed here; it is owed by the
> ε-robust docket work. Until it is fixed, the sentence "ε ≡ 1 bounds the
> defect" is not merely weak but **not meaningful**: without a declared
> normalization there is no scale on which 1 is large, and an engine could
> satisfy any schedule by rescaling its measure. Whatever functional is adopted
> must therefore come with its normalization, so that a certified excess and a
> declared schedule are quantities of the same kind. (The ε-robust docket work
> has since produced a candidate — the uniform distance from the displayed
> prices to the coherent assignments, with a normalization forced by the dual
> rather than stipulated. Adopting it is a decision this revision does not take;
> see the changelog.)

> **(T1.b) Two routes to a working tolerance.**
>
> 1. **Engine-certified modulus.** The engine certifies a computable ε_t → 0
>    with its prices provably ε_t-coherent at every finite time. For the audited
>    logical-inductor engine this is **open in both directions**: no such modulus
>    appears in the source, and no impossibility proof is known. A warning the
>    audit is emphatic about: the adjacent negative result in the literature —
>    that computability, non-dogmatism, Gaifman inductivity, and a very weak form
>    of coherence are jointly unsatisfiable — is **not** this statement and must
>    not be cited as settling it. Both that result and the paper's own
>    three-way impossibility turn on Gaifman inductivity, a desideratum the
>    algorithm already fails; the modulus question involves no Gaifman condition
>    at all.
> 2. **Book-declared working tolerance under T2.** The engine certifies whatever
>    floor it can honour, possibly the vacuous one, and the *book* voluntarily
>    declares a tighter working tolerance, carrying the breach as a chargeable
>    liability. **This is the operating mode**, and it is what makes T1's open
>    status less damaging to the composite than it first appears: the mechanism
>    can run on a useful tolerance without any engine ever certifying one. It
>    does not close the open problem; it prices it.

> **(T1.c) A candidate weakening, stated but not adopted.** T1 could be weakened
> to an *eventually-coherent, rateless* tolerance whose breach semantics is
> quarantine-on-detected-excess rather than schedule conformance. §7 already
> carries quarantine, so the weakening reuses existing machinery. Its downstream
> cost is real and must be paid deliberately: the ε-robust merits certificate
> loses its *a priori* guarantee and becomes *a posteriori* — the docket
> certifies, and a later Farkas check may retroactively quarantine the channel.
> Anything leaning on the certificate being sound at issue time would need
> restating: specifically the recomputation discipline, under which a ruling
> tagged on the merits is rejected unless the program that supports it is
> recomputed rather than merely re-compared, and the merits-iff-leverage
> biconditional, which ties a merits direction to the feasible set built from the
> simplex, the pinned record, and the endorsements as one-sided constraints.

**(T2) Certification layering.** The engine certifies floors (its
ε-schedule and horizons); breach of a certified floor is the *engine's*,
handled by §7. The book may voluntarily declare tighter working tolerances
or deadlines; breach of a self-declared tighter bound is the *book's*, and
chargeable — it assumed the risk.

## 6. Conduct clauses [engine-facing protocol; auditable]

These are conditions on the surrounding institution and its funders, not on
the engine: an otherwise valid engine need not enforce them internally, and
F3/F4 in particular are anti-insider rules of the environment. The organizing
fact: **inquiry chooses what procedure to run; it never chooses what the
procedure returns.** Funding may buy the engine's *attention* — selection,
scheduling, declared parameters — never its *answers*. The assumed half of that
discipline is a corollary of §8; the auditable remainder is:

**(F1) Request-keyed subsidy.** Subsidies attach syntactically to a
**SettlementRequestKey**: (target report variable, or theorem-question for
the logical channel; procedure; funder identity; timing). A request key
names a *question*, never an outcome, so directional funding — "pay to
settle X at v" — is *inexpressible*, not merely forbidden. Funding a
theorem-question funds the decision, both directions, never a one-sided
search. (Forward note: Track C keys requests to QuestionRecords; this
interface depends on no inquiry ontology.)

**(F2) Stopping neutrality.** The funder's stopping policy must create no
directional bias in what gets certified. Two witnesses are named — a
precommitted stopping rule (fixed-horizon experiments), or an
optional-stopping-safe (anytime-valid) certificate — and **the condition is
neutrality; the two are instances, not an entitlement.** Which witnesses are
available is engine-relative, and for at least one serious candidate engine only
the first is: an engine whose soundness guarantee is a global asymptotic
property of an entire price sequence issues no per-request, per-date
certificate, so the anytime-valid route has nothing to instantiate it and the
precommitted rule carries the whole load. Draft 2.1 read as though both routes
were always open; they are not.

**(F3) Probe blackout.** The funder of a settlement request takes no fresh
positions on its target between funding and pin: a blackout window,
disgorgement on violation, and one checkable objection type. *This is a new
conduct type, not an extension of an existing one.* Draft 2.1 described it as
the corpus's insider pattern "extended verbatim"; the corpus has no insider,
blackout, or disgorgement machinery. What it does have is a **conduct** family
whose displayed member is the cross-component transfer objection — a public
fence declaration plus a recorded transfer with typed source and destination,
upheld when the transfer crosses the declared fence, vacuous when the book
declares no fence. F3 is built in that family's shape, with the same
obligations (typed grounds, a finite record check, a declared disposition), but
its content is new here.

**(F4) Funder provenance.** Funding profiles are recorded per pin, feeding
a common-source objection surface when one purse bankrolls all premises of
one conclusion. As with F3, the objection type is new; what it reuses is the
existing per-provenance keying, under which a subsidy is keyed to the
provenance class the token gate already represents and a misdeclared class is
itself objectionable.

## 7. Breach clauses

Detectable breaches: missed certified horizons, tolerance violations (a
Farkas certificate over pinned-plus-priced content beyond the declared
ε_t, once §5's functional is fixed), jurisdiction violations (a pin outside the
declared class, or a second pin on a variable), and gating violations. A breach
is an **authorless cost** — the world cannot be charged — so the clause is cost
allocation:

1. **Toll** — the clocks the breach touches pause; substrate failure never
   converts into unearned book liability.
2. **Quarantine** — the specific channel in breach is frozen or
   downweighted; unaffected channels run on.
3. **Escalate** — persistent breach is constitutional grounds for era
   change, so permanent substrate failure becomes a lawful revolution
   rather than silent rot.

> **A principle, stated because the audit's J2 finding invites the error:
> breach handling is cost allocation, never satisfaction.** A clause is not
> satisfied by the constitution knowing what to do when it is violated. That an
> inconsistent theory's double pin is *detected* and *routed* is a point in the
> design's favour — the one case where the pen can violate write-once is
> precisely the case the breach stack was built for — but it is not inhabitation
> of J2, and an engine relying on it does not satisfy the clause. The same
> applies wherever §7 is invoked: routing a failure is not meeting a
> requirement.

*Housing note.* This stack, and the layering of §5, are declared constitutional
content rather than kernel structure, so revising either later is a lawful
in-system act.

## 8. The assumed residue, split by channel

Every clause above is required to admit a declared audit or certification
procedure. What remains assumed differs by channel, and this section names both
residues rather than hiding either.

**Empirical channel — the faithfulness axiom.**

> **Procedural faithfulness.** *Conditional on the declared procedure, its
> declared inputs, and the realized world, a pin's value has no further
> dependence on anything — in particular, none on the book's states or on
> any funding profile.*

Causally: the book and the funders may *select, schedule, and parameterize*
procedures; they may not touch a procedure's outcome channel except through
its declared inputs and the world itself. This deliberately permits
performativity — an agent whose actions change the world will see pins that
depend, through the world, on its own book; that is faithful measurement of
a world the agent helped make, not manipulation. What the axiom excludes is
any *extra* path from book or purse to pin value. Procedure *reliability*
is deliberately not assumed: procedures are declared content, their quality
is warrant-layer, answerable, and challengeable — only the no-extra-path
clause is axiomatic.

Why an axiom: the record cannot audit its world-channel, and this is argued from
both sides. From inside the mechanism, by the record-extensionality and gauge
results — that two runs with the same public record are indistinguishable to
every record-reading judge, and that the transition structure is preserved under
the declared conjugacies — so world-contact is not a record property. From
outside it, by the deference results, under which manipulation is
counterfactually invisible and bit-identical to honest interaction, with
non-recoverability surviving full policy disclosure. *Locational note:* the
deference results live in the Logical Induction formalization tree, not in the
corpus this document otherwise cites; they are a neighbouring development and
are cited as such. Transparency cannot buy the axiom back.

**Logical channel — checker trust.** Logical pins are **proof-carrying**: a
pin on a theorem-question ships a derivation certificate checkable by a fixed
**proof checker**. Derivation is therefore *auditable*; what remains assumed is
the checker itself (soundness of the checking program) and the boundedness of
discovery (§9). This is not a new commitment: the corpus's judges bottom out in
finite record checkers over a finite meta-depth, so checker trust was a standing
assumption before this document named it.

*Terminology.* Draft 2.1 wrote "proof kernel". The corpus reserves that word for
its own formal object and states explicitly that external phrases such as the
Lean proof checker are **not** names of it, so "checker" is used throughout here.

*A modification this requires of a deductive engine.* Standard deductive
processes emit **sentences, not derivations** — a nested sequence of finite
sentence sets, with nothing shipped alongside. So proof-carrying pins are a
strengthening, logged as Δ₂ in §10: instantiate the process as a proof
enumerator emitting (φ, π) pairs and define the stage sets as the first
projection. The cost is negligible in practice, since every concrete deductive
process *is* a proof search and already computes π before discarding it, and the
market reads only the projection so its guarantee is undisturbed. But it must be
stated rather than assumed.

*Structural remark.* The interface's two assumed residues are exactly the
two world-facing unpayable debts — the **causal debt** at the empirical pen,
the **logical debt** at the checker — and the third debt, the originative one,
never touches the interface at all: it lives in the seed. The composite
guarantee is therefore irreducibly conditional in precisely two named places,
and this is the boundary where alignment work on the substrate ends and
alignment work on the learner begins.

## 9. The deduction-budget clause

*Requirements (adopted).* Under a bounded engine, the logical-relations
input to every credal computation is the engine's **deductive closure so
far**, not the ideal closure of the language. Consequences and
requirements:

- **Partial-closure soundness.** Nothing downstream may assume a
  consequence the engine has not yet pinned. The feasible region is
  accordingly larger than ideal and **contracts as deduction proceeds**:
  deduction is a settlement stream like any other, rateless per (C1).
- **Fundable deduction.** A settlement request may target a
  theorem-question, under the full §6 discipline: the request names the
  question, both directions, never a one-sided proof search.
- **Budgets buy progress, not deadlines.** Deduction funding accelerates
  the stream; it cannot promise rates, per (C1).

*The hole (marked).* The formal content — the budget structure itself, and
the non-exploitability condition an engine's partial logical beliefs must
satisfy *while deduction is incomplete* — is deliberately left open here.
It is the one clause of this interface that only LI-like constructions are
believed to inhabit (a bare prover has pins but no coherent partial belief
between them; that gap is what this clause is *for*), and it is proposed as
the opening formal question of the collaboration.

## 10. Witnesses

*Banner: every row below except the first is a **positioning hypothesis pending
literature and witness audit**. Nothing in those rows is asserted as
established. Row 1 has been audited and its status is stated below the table.*

| engine | pen (J/C) | purse (P) | tolerance (T) | deduction (§9) |
|---|---|---|---|---|
| **budgeted LI — AUDITED** | logical: decidable fragment, rateless; empirical via observation stream | non-exploitation (declared type: market); **P2 inhabited literally by the Budgeter construction** | ε_t > 0 declared; robust forms required; non-vacuity open | (i) met natively; (ii)–(iii) not met |
| infra-Bayesianism | empirical: native | minimax regret (declared type) | exact: convex coherent states, ε ≡ 0 | uninhabited (no logical uncertainty) |
| defensive forecasting (Shafer–Vovk) | empirical streams | Ville-style validity | exact protocol prices | uninhabited |
| conformal engines | empirical: declared class | coverage certificates | exact at the certificate level | uninhabited |
| Kelly-style limiting methods | completeness clause in the abstract | none (pure pen) | n/a | uninhabited |
| bare theorem prover | logical pen + literal compute budget | none | n/a | pins without partial belief — the anti-witness motivating §9 |
| classical Bayes (merging) | complete under realizability | Dutch-book coherence | exact | uninhabited |
| human prediction markets | institutional instantiation of the whole interface | market | market-dependent | crowd deduction, uncertified |

The P2 entry in row 1 is the audit's cleanest finding and the strongest single
piece of evidence that this interface carves at a real joint. It is not an
analogy: the construction defines a computable budgeter which zeroes a trader's
strategy as soon as its value reaches −b in **some** propositionally-consistent
world consistent with the deductive state — a *worldwise* floor, which is
exactly what P2 asks for and strictly more than an expected-value constraint —
and the trading firm then combines an infinite sequence of traders through it
against a summable budget schedule, so aggregate exposure is bounded. P2's
phrase "bounded aggregate trader budgets where it may not refuse" reads as
though written with this construction in view.

The fact that existing frameworks naturally inhabit *different subsets* of
the clauses is evidence that the interface is exposing real modular
structure — with the two serious candidates from the alignment literature,
LI and infra-Bayesianism, sitting on opposite sides of the
logical/empirical line. Their composition into a single full witness is an
open problem this interface makes precise.

### B3, restated to the pair

The audit's central mapping decision: **budgeted LI is not one object at the
interface boundary. It is a pair, and the pair straddles the boundary.**

| LI object | interface role |
|---|---|
| the deductive process **D** — a computable nested sequence of finite sentence sets | **the pen and the clock** |
| the market **P** — a computable sequence of pricings into ℚ ∩ [0,1] | **the purse, the tolerance, and the certificate type** |

The alternatives are worse. Making the market the pen would key pins to prices
reaching 1, an event nothing guarantees at any finite time — only the limit is
coherent — so write-once would have no well-defined trigger. Making D the whole
engine leaves P1–P4 and T1 with no referent at all, since D has no prices, no
budget and no tolerance. This split is the only assignment under which every
clause has a candidate inhabitant.

> **B3 (restated).** Let ⟨D, P⟩ be budgeted, finite-trader LI, with D a declared
> deductive process and P a market satisfying the logical induction criterion
> relative to D. Then ⟨D, P⟩ inhabits
>
>   **SI⁻ = { J1, J3, C1, C2, C3, P2, P3, P4, T2, F2-via-precommitment, §9(i) }**
>
> under the pen/purse split above, where C3 holds **vacuously on the logical
> channel** (there are no upstream horizons for an adequacy inequality to be
> adequate to, so the work is carried entirely by C2's tolling), and F2 is
> discharged by the precommitted-stopping witness only.
>
> Two clauses sit outside SI⁻ as **named conditionals** rather than
> inhabitations:
>
> - **J2**, conditional on the **consistency of the declared theory** (§2). This
>   hypothesis is named explicitly and is not discharged: consistency of a theory
>   is not provable within it.
> - **P1**, conditional on **Δ₁**.
>
> Outside SI⁻ entirely: **T1** (open, §5), **§8's logical-pin certificate
> requirement** (needs Δ₂), and **§9(ii)–(iii)** (needs Δ₄).
>
> Conditions Δ₁, Δ₂ and Δ₃, **together with consistency of the declared
> theory**, are jointly sufficient for the full interface **excluding §9**,
> whose requirements (ii)–(iii) additionally need Δ₄. Consistency has to appear
> in this list precisely because J2 was pulled out of SI⁻: with J2 inside the
> set, as the audit arranges it, consistency rides along as a qualifying bullet;
> with J2 outside, sufficiency must name it or it goes missing.

B3 as worded in draft 2.1 ascribed the property to "budgeted LI" as a single
engine. It must be ascribed to the pair, because the J/C clauses and the P/T
clauses are satisfied by different objects, and a reader who conflates them will
think the market supplies the pen.

### The delta list

| Δ | statement | class | cost |
|---|---|---|---|
| **Δ₁** | a declared core floor θ_min that remains satisfiable under the relative reading as the deductive state grows and the region contracts | **open sub-problem** — neither modification nor weakening until someone determines which | Unknown. Nothing bounds the induced region's geometry; the per-date check of P1 is a program, but persistence is not. |
| **Δ₂** | instantiate D as a proof enumerator emitting (φ, π) pairs, with the stage sets the first projection | **modification**, negligible | Near nil: concrete processes already compute π. The market reads only the projection, so its guarantee is undisturbed. |
| **Δ₃** | either **(a)** a computable ε_t → 0 with prices provably ε_t-coherent at every finite time, or **(b)** the T1.c weakening to eventually-coherent-rateless with quarantine-on-detected-excess | (a) **modification**, existence open · (b) **weakening** | (a) unknown. (b) the merits certificate becomes *a posteriori*; the recomputation discipline and the merits-iff-leverage biconditional need restating. |
| **Δ₄** | funding-responsive deduction: a budget-indexed family of processes, with the criterion restated relative to the realized process | **modification**, substantial | **Reserved** — this is §9's marked hole and is not costed here. |

Δ₄ has **two inequivalent versions**, and the interface does not choose between
them: *acceleration*, where the process is fixed and a budget buys progress
along it by wall-clock, and *attention*, where the budget selects what the
process works on, making the stream itself endogenous to the funder. Only the
second makes the plausible-world set funder-dependent, and only the second
threatens the criterion's statement. Distinguishing them is part of §9's
reserved work.

**Order two, on the audit's counting** — but only if Δ₂ is priced at its true
(negligible) cost and Δ₄ is set aside as reserved. The two that carry weight are
Δ₁ and Δ₃.

## 11. How the composite guarantee cites this document

The target guarantee (stated in full in E3) is a **conditional visibility
guarantee**: *given an engine satisfying the settlement interface,* the
learner's endorsed normative state evolves through a process in which —
empirical and logical influence is non-exploitable in the engine's declared
certificate type; practical silence, reflective neglect, and emptiness have
visible, priced consequences; prior answerability survives revision and
migration; normative force enters only through auditable endorsement; and
recognized grounds for inquiry or revision cannot be silently bypassed. No
conjunct is a behavioral prediction; each says what the record must show.

### The compiler contract — a second hypothesis block

*Candidate name, flagged for the author's confirmation rather than asserted.*

Work restating the corpus's conditional composite over an arbitrary
interface-satisfying engine found that the engine clauses **do not exhaust** the
composite's antecedent. Four conditions of the corpus's condition bundle have no
interface counterpart, and they are not properties of a world-channel at all —
they are conditions on the *compiler* that stands between the engine and the
mechanism. Presenting them inside the interface would misattribute them to
engines; leaving them unstated would make the clause list look complete when it
is not. So they are named here as a distinct block:

1. **Publication before demand** — each date publishes its rational compact
   convex region before demand, prefix-causally.
2. **Coherent extension to fresh sentences** — the retained world mixture
   extends coherently to sentences newly queried.
3. **A summable drift schedule** — reference drift is bounded by a computable
   schedule with finite total.
4. **A solver budget** — the constrained quote's selection errors sum to a
   finite total. *This is not T1.* T1 bounds how far the engine's **prices** may
   be from coherence; the solver budget bounds how far the **compiler's chosen
   quote** may be from the constrained optimum. Neither implies the other, and
   the corpus bundle carries only the second while the interface carries only
   the first — a gap in both documents, visible only once they are laid side by
   side.

With the block named, the composite reads in three parts: **the engine satisfies
the interface, the compiler satisfies its contract, and then the bound holds.**
That is the honest shape, and it is why the composite's hypothesis list is
longer than its clause list.

## 12. Appendix: decision provenance

Draft 2.1 carried a full decision-provenance table. It is compressed here to a
note, since the decisions are settled and the detail belongs to the decision
ledger rather than to the interface.

The clause set derives from five agreed decisions — reports-only jurisdiction;
write-once/owner-only exclusivity; the toll→quarantine→escalate stack; ripeness
with tolling; and certification layering — of which the last two are held
loosely and housed as constitutional content. Draft 2 adopted six review
corrections: the valued-report-variable pin type, the write-once reformulation,
the two-channel split of the assumed residue with proof-carrying logical pins,
conditional faithfulness in place of blanket independence, the
SettlementRequestKey in place of question keys, and stopping neutrality in place
of an e-value mandate. Draft 3 adopts the audit's corrections, itemized in
`SI_V3_CHANGELOG.md`. The §8 residues remain undecidable by design: named, not
hidden.

## 13. Open items

1. The §9 hole: budget structure and non-exploitability under incomplete
   deduction, including the acceleration/attention distinction (the
   collaboration's opening formal question).
2. **Δ₁** — persistence of a declared core floor under region contraction. The
   per-date check is settled; the infimum over time is not.
3. **Δ₃(a)** — a computable coherence modulus, or a proof that none exists.
   Open in both directions; the adjacent impossibility does not settle it.
4. The finite-time defect functional and its normalization, owed to §5 by the
   ε-robust docket work, together with the decision whether to adopt the
   candidate that work has produced.
5. Witness composition: a single engine inhabiting both sides of the
   logical/empirical line.
6. Cert_e(H, C): the abstract certificate-semantics relation (P4's
   formalization target).
7. Confirmation of the **compiler contract** as a named block (§11), and whether
   its four conditions belong in this document at all or in E3.
8. The literature audit for §10 rows 2–8, which remain positioning hypotheses.

## What v3 does NOT claim

**SI⁻ is an audit outcome, not a proved theorem.** It is the result of a
clause-by-clause reading of one engine's source against this document. Producing
it is not proving B3; **B3 remains to be proved**, and this document only says
what its statement should be and which clauses it can hope to cover.

**Nothing here proves the composite guarantee.** §11's conditional visibility
guarantee is untouched. Establishing that an engine satisfies the interface is
the *antecedent* of that conditional, not the conditional.

**Δ₁ and Δ₃(a) are open**, and are the two conditions that carry weight. Δ₁ is
unaudited beyond its statement: whether a declared floor survives region
contraction is a question about the geometry of the region an engine's prices
induce, and the per-date program in P1 narrows that question without answering
it. For Δ₃(a) neither a modulus nor an impossibility proof is known.

**§9's formal content is deliberately absent.** The three adopted requirements
are stated and audited — (i) met natively by the audited engine, (ii)–(iii) not
met — and no formal content is proposed for the budget structure or for
non-exploitability under incomplete deduction.

**No verdict here rests on the behaviour of any implementation.** Every claim
about the audited engine is traceable to a definition or theorem in its source;
every claim about the corpus is traceable to a result verified to exist in the
trees, per the citation table in the changelog. Where a result could not be
found, the changelog says so rather than inferring one.

**Rows 2–8 of §10 remain positioning hypotheses.** Only row 1 has been audited.
