# The moving-correspondence bundle against the settlement interface

The frozen corpus states its conditional composite over one named condition
bundle, `C-MOVING-INTERFACE`, and the joint theorem inherits that bundle
wholesale: its Logical Induction boundary says a corollary is available "only if
every condition of `C-MOVING-INTERFACE` is separately supplied". The settlement
interface asks for something different in kind — a class of engines, described
clause by clause.

This table is the check that the two descriptions line up, condition by
condition. It is delivered as a table rather than a paragraph because the
interesting entries are the ones that do **not** line up, and a paragraph would
let them pass as prose.

Two rules were applied throughout. A relation is recorded in the direction it
actually holds, not in the direction that would be convenient. And a condition
with no interface counterpart is a **finding**, recorded as such, not a
footnote — because the parametric composite has to carry it as an explicit
hypothesis, and a reader who does not see it here will not know why the
hypothesis list is longer than the clause list.

The machine-readable form is `src/parametric_composition.py::MOVING_INTERFACE_MAP`,
and `tests/test_parametric_composition.py` checks that this document and that
table name the same rows.

---

## 1. Condition by condition

The bundle's clock condition is split into two rows, because its two halves land
in completely different places.

| # | bundle condition | interface clause(s) | relation | reading |
|---|---|---|---|---|
| MI-1 | fix a computable deductive process | J1, C1-logical | **implied by the interface** | J1 puts the process on the public record and C1-logical quantifies over "the declared deductive process". The interface supplies this, once *declared as public record* is read as effective presentation. |
| MI-2 | each date publishes before demand a rational compact convex region | — | **no counterpart** · FINDING | Publication before demand is a quote discipline on the mechanism, not a property of a world-channel. No clause asks for it. |
| MI-3 | a rational witnessed reference and a fixed positive core coefficient, with the core condition against the ambient simplex | P1 | **bundle strictly stronger** · FINDING | Stronger in two independent ways. It fixes the coefficient where P1 admits a varying core with a certified minimum; and it reads the core against the ambient simplex, which voids on the first exact pin (`NL-SI-8`). |
| MI-4 | coherently extends its retained world mixture to fresh queried sentences | — | **no counterpart** · FINDING | A compiler property about language growth. T1 is adjacent but governs the tolerance of prices already displayed, not extension to new sentences; neither implies the other. |
| MI-5 | bounds reference drift by a summable schedule with finite total | — | **no counterpart** · FINDING | Supplied downstream rather than by any engine: the movement recursion gives each of the at most `Psi_0` reference jumps its majorant and sums them. Mechanism-side. |
| MI-6 | computes a constrained quote with errors summing to a finite total | T1 | **neither direction** · FINDING | The bundle *does* carry an error budget — but a **solver** budget on quote selection, not a tolerance on how incoherent the engine's prices may be. The bundle has no coherence-tolerance clause; T1 has no solver-error clause. |
| MI-7a | preserves the rational prefix-causal clock | C2, C3 | **neither direction** | Incomparable. Prefix-causality is a constructibility discipline the interface never states; ripeness, tolling and adequacy are docket structure the bundle never states. |
| MI-7b | preserves the aggregate downside limit of two | P2 | **equivalent modulo the constant** | The cleanest correspondence in the table. The bundle's constant is P2's declared limit with the value fixed at two. |
| MI-8 | uses an aggregate trading field with the declared dominance property | P4 | **bundle strictly stronger** · FINDING | The bundle hard-codes trader vocabulary. P4 declines to, asking only that a certificate type be named and the guarantee stated relative to it. The bundle's condition is one instantiation of P4. |

## 2. Interface clauses the bundle never needed

Twelve of the eighteen clause texts are untouched by the bundle. This is the
larger half of the finding: the bundle is not a weaker interface, it is an
interface for a different and much smaller job — one deductive process, one
language, one market, no institution around it.

| clause | never needed because |
|---|---|
| J2 | write-once, owner-only. The bundle has **no exclusivity formulation at all**: nothing in it prevents a variable being settled twice. |
| J3 | migration transport. The bundle is stated inside one fixed language. |
| C1-empirical | funding-responsive completeness. The bundle's channel is purely deductive. |
| C3 | adequacy. The bundle relates no downstream deadline to an upstream horizon. |
| P3 | finite gating. The bundle quantifies over an infinite enumerated trader family and never bounds what is live per date. |
| T1 | the coherence tolerance itself, as distinct from MI-6's solver budget. |
| T2 | certification layering. The bundle has no notion of who carries a breach. |
| F1 | request-keyed subsidy. |
| F2 | stopping neutrality. |
| F3 | probe blackout. |
| F4 | funder provenance. |
| S8-logical | proof-carrying pins. The bundle's process emits sentences, and nothing asks it for derivations. |

## 3. What the table settles

**The mapping is not an identity.** Of the nine rows: one is supplied by the
interface (MI-1), two are strictly stronger than any clause needs (MI-3, MI-8),
three have no counterpart at all (MI-2, MI-4, MI-5), two are incomparable (MI-6,
MI-7a), and exactly one is a clean correspondence (MI-7b). Twelve clause texts
are never exercised.

**Where the strictness bites.** MI-3 is the row that matters, and it is worse
than "stronger than necessary". Its ambient reading is not merely a demanding
version of P1 — under settlement it is *unsatisfiable*, for every positive
coefficient, from the first exact pin onward. The relative reading is what an
engine can certify, and the transport lemma is the sense in which it is stable.
A composite stated over the ambient reading would have an antecedent nothing can
inhabit once anything is settled.

**Where the gaps go.** Four conditions are carried as explicit hypotheses of
the parametric composite — the three with no counterpart, and MI-6, whose
adjacent clause governs a different quantity and so does not supply it. None
becomes an engine clause, because none is a property of a world-channel. Each is
listed in the composite's statement and named in its refusal message when
absent. That is the honest disposition: the interface did not silently acquire
them, and the theorem does not silently drop them.

**A consequence for the interface, not just for the bundle.** MI-6 exposes that
the corpus never had a coherence tolerance and the interface never had a
solver-error budget. Each is a real requirement; neither document carries both.
The parametric composite therefore carries the solver budget as a hypothesis
even though every engine clause is discharged. That is not a fault in either
document, but it is worth stating before someone reads the clause list as
complete.
