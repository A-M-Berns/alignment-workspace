# Integrity

**Status: canonical; Established `lean-proved`** for the conservation theorem, the
propagation law, receipt immutability, faithful carry, and the multiplicity witness.
The protocol's predicates are typed inputs, stated below as such.

## The role

A cognitive trajectory that can rewrite its own past can escape anything. It need not
refuse a criticism; it can misremember having received it, re-anchor the debt to a
specification that is easier to meet, mint the authority it needs, or retire the
vocabulary the obligation was stated in. Every step is locally defensible and the
obligation is gone.

**Integrity** rules this out:

> A cognitive trajectory cannot falsify or silently rewrite its own normative history.

It is a relation between two *accounted obligation states* of one history. It says
nothing about whether the record is good, whether the right things reached it, or
whether anyone outside was allowed to challenge it. Those belong to
[Robust Openness](Openness-Coverage-and-Non-Capture).

## The protocol

Everything Integrity reads is supplied by an application as a **protocol**: a type of
resolution witnesses for each requirement, a type of settlement items, a type of
warrants (the rule, licence and interpretation bundle an authority acts under), and
six predicates over history prefixes — admission of an occurrence with its anchor,
liveness of a port, a warrant being in force, adequacy of an answer, availability of a
settlement item through the external boundary, and the internal closure judgment
that an available item suffices to close a requirement. Two typed facts connect them:
an adequate answer resolves the requirement, and an available item with a closure
judgment resolves it.

A **resolution witness** is evidence that a requirement has been *legitimately
accounted for*. An adequate answer yields one; so does a valid closure. The two are
different fates — `answered` and `closed` — and no theorem identifies them. A
settlement-backed discharge is not an answer to the underlying question, and the
theory never says it is.

Nothing here authenticates a protocol. That the predicates mean what they say is the
semantic-authentication input, named as such and never derived.

## The accounted obligation state

At a prefix, the state `O` is:

- the **boundary**: the authenticated history prefix, the finite set of **exposed
  occurrences** — every obligation ever incurred, by immutable identity — and the
  **live docket**, a finite family of ports each demanding some content;
- the **anchor** of each occurrence, fixed at admission and never redefined;
- the **account** of each exposed occurrence: a finite tree whose leaves are exactly
  the three fates — a live port, an authenticated answer receipt, or an authenticated
  closure receipt — and whose internal nodes are authenticated **local laws**
  transforming one requirement into successors.

Occurrence identity lives outside the content type. Two occurrences with the same
anchor have two accounts, and nothing in the theory can identify them; a single
receipt discharges two occurrences only if a transition explicitly routes both of
their ports to it. There is no additive or lattice layer over content because
multiplicity is in the index.

Every receipt and every law carries an **authority**: a fresh event at a strict
prefix, citing only prior grounds, under a warrant in force there. A transition
cannot cite itself. A closure receipt stores the settlement item, its availability at
that prefix, and the closure judgment made at that prefix; a later change of rules or
interpretation cannot alter whether a historical discharge was properly certified,
because the certificate is data in the account, not a predicate recomputed later.

A **local law** carries maps of resolution witnesses in both directions: resolving
every successor resolves the parent (faithful carry, no loss) and resolving the
parent resolves each successor (no growth). Carry, split, refinement and
re-representation are instances; a disposal under the Defeat Principle is the
identity law with the grounds recorded in its authority. Local laws are unary in the
parent: a genuine aggregation of two distinct parents into one successor that only
their joint resolution resolves is not expressible, and is filed as an extension
rather than adopted.

## Integrity evolution

A **transition** is one fresh event appended to the history that supplies, for every
live port of the docket it starts from, an account at the docket it produces, and
admits fresh occurrences only with an admission credential and a live port demanding
their anchor. There is no field by which content leaves.

An **Integrity evolution** from `O₀` to `O₁` is a chain of transitions in which every
intermediate state is explicit and every target account is *the propagation* of its
source account through the transition: substitution at live ports for occurrences
already exposed, a fresh live account for new ones. The target account is therefore
a function of the source account and the certificate; there is no freedom to choose
it, and two witnesses cannot disagree about either endpoint. Evolutions compose at a
literally shared state. An initial state is one way to construct a first accounted
state, not a premise the relation needs.

## Answerability Conservation

The theorem, for any Integrity evolution from `O₀` to `O₁`:

- **no occurrence disappears** — the exposure of `O₀` is contained in that of `O₁`,
  and since occurrences are elements of a finite set, distinct ones stay distinct;
- **receipts persist** — for every occurrence exposed at `O₀`, the terminal answer and
  closure receipts of its account at `O₀` are among those at `O₁`;
- **live content is transported faithfully** — there is a transport of live-port
  resolutions from `O₁` back to `O₀` under which every account at `O₁` denotes what
  the account at `O₀` denoted;
- **anchoring is by type** — each account is an account *of its occurrence's anchor*.

This is the three-fate conservation stated at the level where it is a consequence of
the type rather than a clause: the only leaves are the three fates, and a transition
can only substitute at live ones. The lattice-valued content-conservation clause that
an earlier formulation required is now an instance of this, and the countermodels
that showed record integrity alone insufficient are the reason the account type has
the constructors it has.

## What is blocked, and by what

| evasion | what blocks it |
|---|---|
| an unchecked "answered" label | an answer leaf needs an adequacy certificate at a strict prefix |
| self-grounded or unauthorized disposal | every node carries an authority: fresh event, prior grounds, warrant in force |
| manufactured settlement or closure | a closure leaf needs external availability and the internal judgment, both stored |
| retroactive recomputation of a closure | the judgment is data in the receipt at its own prefix; substitution carries it unchanged |
| an empty ledger passing vacuously | an initial state needs an admission credential and a live port per exposed occurrence; there is no empty account |
| segment witnesses that disagree at a boundary | evolutions are indexed by their states and compose only at a shared one |
| collapsing two equal-content occurrences | accounts are occurrence-indexed; the witness with one anchor and fates `{answered}`, `{live}` |
| weakening or making a successor unanswerable | a local law carries both maps |

## Integrity is not Non-Capture

> **Integrity:** did the process faithfully preserve and account for what entered it?
>
> **Non-Capture:** could the process improperly control what was *able* to enter,
> challenge, or evaluate it?

A history can have perfect integrity while the process behind it ensured nothing
awkward was ever admitted, or lost the protected party's standing on a successor
whose content it preserved exactly. Standing and access are the subject of
[Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture); Integrity's
liveness credential is the record fact that a port is open, not a standing claim.

---

**Evidence.** The account, transition and segment types, the propagation law, receipt
immutability, faithful carry and the multiplicity witness are
[`OccurrenceIntegrity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean);
the accounted state, the evolution relation and the conservation theorem are
[`LegitimateEvolution.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean).
The registered claims are `legitimacy.evolution-conservation`,
`legitimacy.propagate-to-segment`, `legitimacy.receipts-immutable`,
`legitimacy.faithful-carry` and `legitimacy.multiplicity-witness` in the
[normativity claims registry](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/CLAIMS.md).
The countermodels that fixed the constructor list are the integrity adversary round's
[`ATTACKS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-integrity-adversary/ATTACKS.md),
and the lattice-ledger formulation they were run against, now an instance, is the
integrity constructive round's
[`DEFINITIONS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-05-integrity-constructive/DEFINITIONS.md).
The older successor-and-ancestry trace model on which the Defeat Principle was first
checked remains as evidence in
[`NormativeContinuity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NormativeContinuity.lean).
