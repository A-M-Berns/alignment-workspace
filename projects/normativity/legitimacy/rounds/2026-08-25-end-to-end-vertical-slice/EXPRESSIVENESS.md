# Where rich normative forms land

`ARCHITECTURE.md` is this round's canonical account of the objects; this
document assumes it.

Each row classifies one expressiveness case against the two waists. The
classification is a design argument supported by the finite witnesses named in
the last column; no row is a theorem.

Categories: **fits** — expressible in the current waist as it stands ·
**upstream** — belongs in normative practice and reaches the waist only as
issuance, exposure, or non-exposure · **local** — a contained extension that
does not change the waist's shape · **failure** — the waist cannot carry it.

| case | verdict | how |
|---|---|---|
| scalar policy value | fits | one exposure, one LUV | `toy.registry` |
| stakeholder-specific value | fits | one query per stakeholder, one LUV each | `variants.plural_value` |
| plural value, several dimensions | fits | several LUVs; nothing adds across them | `test_value_waist.PluralValue` |
| lower/upper estimates for an incomplete specification | fits | two queries, two LUVs, two inequalities | — |
| value of information | fits | an ordinary bounded observable, if the specification can expose one | — |
| surrogate-goal value | fits | a distinct query with a distinct LUV name | — |
| future endorsement | fits | a LUV whose thresholds are sentences about a later state | `variants.reflective_luv` |
| reference to a superseded specification | fits | the name is the specification's; nothing reinterprets it | `test_toy.ValueRevisionIsNotOperativeRevision` |
| reflective / future-price LUV | fits | the waist does not notice; the certificates are the burden | `variants.reflective_injunction` |
| mixed `Prob`/`Expect` injunction | fits | one inequality over both | `toy.j0` |
| affine tradeoff between value dimensions | fits | one declared inequality mixing signs | `variants.plural_affine_tradeoff` |
| several active value specifications | fits | quantities are named per specification; no arbitration | `variants.two_active_specs` |
| a query that cannot be quantified | fits | `NonExposure`, a representable state | `variants.failed_query` |
| an observation with no exact reading | fits | `sem_L` returns the empty set | `variants.uninterpreted_outcome` |
| **conditional obligation** | local | see §1 | — |
| **disjunction of demands** | upstream / local | see §2 | — |
| **lexicographic priority** | upstream | see §3 | — |
| **defeasible priority** | upstream | see §4 | — |
| **nonconvex permissibility** | upstream / local | see §2 | — |
| **value incomparability** | upstream | see §5 | `test_value_waist.PluralValue` |
| **dynamic ontology revision** | upstream | see §6 | `variants.unrelated_language_extension` |

---

## 1. Conditional obligation

"If `phi`, then `Expect(X) <= c`" is not an affine inequality, and the waist
refuses it as written.

Two readings, and they are genuinely different obligations rather than two
encodings of one.

**The condition is normative.** "Once it is settled that `phi`, this ceiling is
in force." Then the condition belongs upstream: the obligation is issued as an
unconditional injunction by a normative event whose derivation cites the reason
occurrence that `phi` was settled. The waist is untouched, and the record gains
what it should have anyway — an event, an author, and a basis for the ceiling
having come into force.

**The condition is cognitive.** "The ceiling binds in proportion to the
market's credence in `phi`." This is `Expect(X) <= c + (1 - P(phi))`, which is
affine and fits. It is a weaker demand than the first reading, and saying which
was meant is normative work the waist should not be doing.

**Genuinely conditional force** — the ceiling holds at prices where `phi` is
priced high and not where it is priced low, with no fixed slope — cuts the
region along a nonconvex boundary and is §2.

## 2. Disjunction and nonconvex permissibility

`A or B` where each is a region is a union, and a union of half-space
intersections is generally nonconvex. Three facts bound what can be done.

`K^N` is convex by construction. `K^D` is a convex hull. The traderization
schedule's region is `RationalPolytope`, a convex hull of rational vertices, and
the enforcement trader's conformance argument is about row violations.
**Nonconvex permissibility has no representation anywhere in the current
execution layer**, so this is not a waist question.

What can be done: the disjunction stays upstream, and the choice of disjunct is
a normative event. Issuing `A` is one injunction; later replacing it with `B` is
a supersession with its own reasons and its own answerability. That is a
faithful reading of most real disjunctive permissions — the agent may do either,
and which it is doing is a fact someone is answerable for — and it is strictly
more informative than a region that would have permitted both silently.

What cannot be done inside the waist: a single standing payload whose region is
a union. Its convex hull is a weakening, and shipping the hull would be an
invisible weakening under O1's own prohibition. A **local** extension that
*could* be honest is a payload carrying a finite list of alternative row systems
with the selection made by an explicit event; the region enforced is then always
one of them, and which one is answerable. Nothing in this round needed it.

## 3. Lexicographic priority

"Satisfy `A`; among those, satisfy `B`" is an optimisation over a region, not a
region. The operative layer chooses what region is in force and the trader
imposes it; neither selects a point.

It stays upstream in the same way as §2: the lexicographic policy is a rule for
*issuing* injunctions, and its output at a date is an ordinary region. Compiling
the rule itself into the waist would put a solver inside operative semantics.

## 4. Defeasible priority

Defeat is the reason layer's, and the workspace already has it there: the
reason-state round's substrate carries undercutting as an ordinary reason for
`~App(sigma, c@n)` with no attack primitive. An injunction defeated is an
injunction superseded, by an event.

The prohibition in the dispatch — do not let conflict automatically weaken force
— is what makes this the only available reading. When two active injunctions
conflict the round reports `B-empty-intersection` with a certificate naming
both, and stops. Resolving it is jurisprudence and takes an event.

The cost is real and worth stating: between the conflict and the event, the
system has an empty demand and no region to enforce. The architecture makes that
state visible rather than papering over it, and what should happen during it is
not answered here.

## 5. Value incomparability

Preserved by construction, because the waist never scalarises: `n` dimensions are
`n` LUVs, and there is no operation that combines them. A tradeoff appears only
when an inequality with mixed signs is written into an injunction, at which
point the exchange rate is declared, the event that declared it is on the record,
and someone is answerable for it.

This is the case where the architecture does best. Incomparability is not
represented by a special construct; it is what the absence of a construct means.

## 6. Dynamic ontology revision

Two halves, and they separate cleanly.

**Growth of the language away from the fragment** changes nothing: new atoms,
new stage sentences and a new settlement about them leave coordinates, rows,
`K^D`, `K` and live-world deficit identical. Verified.

**Revision of what a quantity means** is not available and should not be. A LUV
is a threshold family, and the family is determined by the specification and
query that produced it. Wanting `X[v0:q]` to mean something new is wanting a new
quantity, which is `X[v1:q]`, and the injunctions naming the old one keep naming
it until an event says otherwise. That is the whole content of Stage B.

The residue: an ontology change can make an old quantity's *thresholds*
undecidable in the new theory, so `sem_L` reveals nothing further about it while
old injunctions still constrain it. The record stays coherent — the quantity has
no settled value and the market prices it freely — but nothing here says whether
an injunction over a quantity the practice has stopped being able to settle
should stay in force. That is an inquiry-layer question and it is filed.

---

## What the table is evidence for

Eleven of the twenty cases fit as the waist stands, and the sample was chosen to
be hostile. Of the six flagged cases, four are upstream for reasons internal to
the architecture's own commitments rather than for want of expressiveness — a
solver, an arbitration rule, and a defeat calculus are each things the operative
layer is specified not to contain. Two admit local extensions that keep the
waist's shape, and neither was needed.

The case that would have counted against the waist is nonconvex permissibility,
and it does not, because nonconvexity is refused by the execution layer's
geometry rather than by the waist. That is a limit on the architecture, and it is
in a different place than this round was looking.
