# Theorem map

Statuses as the line uses them: `PROVED (single derivation)` for a derivation
given here, `MACHINE-CHECKED (stated finite scope)` for an exhaustive enumeration
over a declared domain, `WITNESS` for a displayed instance, `CITED`,
`CONJECTURE`, `OPEN`.

No Lean: the execution environment has no toolchain. Port targets are filed.
All names are **provisional**.

---

## 1. Definitions

**Provenance `P`.** A ground is `(id, content, scope, basis, origin, time)`.
`Pi_t(g, c)` holds when the basis graph from `g` is well-founded, every root has
`origin = conferred` by an external source, every derivation step satisfies
`scope(child) subset bound(parents)`, every basis is strictly earlier, `g` is
undefeated at `t`, and `c in scope(g)`.

The split that makes this a condition rather than a label: **content is free and
scope is not**. Any ground may assert anything — inference, proof, conceptual
innovation and genuine defeaters are all new grounds the reasoner makes itself —
and a derived ground's jurisdiction is bounded by its parents'. So a reasoner may
manufacture reasons and may not manufacture authority.

`bound` has two readings, and the round found they differ (§4).

**Inquiry adequacy `I`.** Three parts, not one:

    encounter --G--> generated inquiry --E--> entitled --service--> docket or backed refusal

`G` (generation) and `E` (entitlement) are **state coordinates**, so revising
them is a transition subject to `P` and `RR`. Service is bounded by a window and
a capacity. **Docketing creates a liability**, which is what connects this
condition to the next: an inquiry obligation, once taken up, is answerable like
any other.

Entitlement is read **at the date the inquiry was generated**. That choice is the
whole content of the condition's defence against attack D, and reading it at
service time instead makes the same trajectory pass.

**Reasons-responsiveness `RR`.** Each moved coordinate is covered by a cited
ground whose content the reasoner's own bearing relation says bears on it, with
the bearing relation read from the state *before* the edit, so an edit cannot
install the bearing that licenses itself. The state includes `bearing`,
`adequacy`, `generation` and `entitlement`, so `RR` applies reflexively to the
machinery that decides what `RR` reads.

There is no cost coordinate anywhere in the state. The previous round enforced
cost-blindness with a raising accessor; here the field does not exist.

**Diachronic answerability `DA`.** The conserved object is a **forest**, not a
label (§3). Every leaf of a liability's descent forest is live, suspended with a
route, or terminal with backing; refinements name successors; identifiers are not
reused; nothing acts on a closed branch.

**Procedural legitimacy `L*`.** In `L_STAR.md`, stated against an environment and
not against these conditions.

---

## 2. Provenance results

**PR-1. No authority amplification.** `PROVED (single derivation)`;
`MACHINE-CHECKED` over all `4^3 = 64` scope chains of length three on a
two-coordinate space.

*Statement.* If `Pi_t(g, c)` holds then `scope(g)` is contained in the union of
what `g`'s roots were granted.

*Proof.* Induction along the basis DAG, which is well-founded because `Pi`
refuses a cycle and requires strictly earlier bases. At a root, scope is what was
conferred. At a derived node, `scope subset bound(parents)`, and each parent's
scope is contained in its roots' grant by hypothesis; unions of containments are
containments. `square`

*Consequence.* **Attack A is defeated.** A chain of any length cannot end with
jurisdiction its root lacked. Necessity: with the amplifying link removed the
same chain is admitted, so the condition refuses the amplification and not the
derivation.

**PR-2. Cycles are refused, and refusal is decidable.** `WITNESS`. Two grounds
each deriving authority from the other yield `provenance.cyclic_basis`; the walk
carries its own path, so a cycle is a verdict rather than a hang. **Attack B is
defeated.**

**PR-3. A self-filed root is refused.** `WITNESS`. The one act closed to the
reasoner is writing down its own root authority. Everything else about a ground —
its content, its being new, its being inconvenient for someone — is open.

**PR-4. The two scope disciplines come apart.** `WITNESS`. A child of two parents
with disjoint scopes is admitted under the union reading with joint jurisdiction
neither parent had, and refused under the intersection reading. Which is correct
depends on whether the constraint being licensed is coordinate-wise or joint, and
**nothing in the condition decides that**. Recorded as an open modelling choice
rather than resolved by fiat.

---

## 3. Answerability results

**DA-1. The single-label fate is not branching-safe.** `WITNESS`. After
`l -> {l1, l2}` with `l1` discharged and `l2` live, the previous round's fold
returns `live` and carries no backing: the discharged branch and its witness are
dropped. Over the length-three sweep, `36` of `343` accepted histories have leaves
of more than one status and `20` have a terminal branch the label omits.

This is a correction to `rounds/2026-08-12-legitimacy-architecture/`, whose
conservation statement is true as stated — it is about a label — and whose label
loses information the audit wants.

**DA-2. Branching conservation.** `PROVED (single derivation)`;
`MACHINE-CHECKED` over all `7^3 = 343` mode sequences, refusing `254` of them when
the backing fields are stripped.

*Statement.* Under the condition, every leaf of a liability's descent forest is
live, suspended with a route, or terminal with backing; the three are exclusive
and exhaustive.

*Proof.* Induction on dates over the frontier. `carry` and `reinstate` preserve a
branch, `refine` and `identify` replace one branch by its named successors,
`suspend` marks with a route, `discharge` and `lose` close with backing and are
refused without it. Every branch is in the frontier or closed, and no mode leaves
one in neither. `square`

**DA-3. Forest composition.** `MACHINE-CHECKED` over all `2401` segment pairs.
Composing the first segment's forest with the second segment agrees with folding
the whole history: `F_{0->T} = F_{s->T} . F_{0->s}`. Endpoint audit needs the
first forest and the second segment, not a replay.

---

## 4. The sufficiency verdict

**SF-1. `P + I + RR + DA` does not entail `L*`.** `WITNESS`, six times.

Six trajectories satisfy all four conditions and fail the target, in three
families, and the families are the finding:

| family | attacks | which relation drifted |
|---|---|---|
| the reasoner's inquiry machinery vs what arises | C pre-emptive generation, E narrow formulation | `generation`, `entitlement` |
| the reasoner's bearing relation vs what bears | G derived defeaters | `bearing` |
| the reasoner's adequacy relation vs what settles | H branch-selective, I distinction collapse, L adequacy narrowing | `adequacy` |

In every case the reasoner used authority it genuinely held, over a coordinate
the grant covered, by a derivation that was well-founded, and revised a relation
of which it holds the only copy the conditions can read.

**SF-2. Why no fifth conjunct closes it.** `PROVED (single derivation)`.

*Statement.* Let `C` be any predicate of the trajectory. There are two
environments differing only in whether the reasoner's adequacy relation is
faithful, on which `C` takes one value and `L*` takes two.

*Proof.* `record_equivalent_pair` supplies one trajectory and two environments.
`C` is a function of the trajectory, of which there is one, so `C` is constant;
`L*` is `True` on the first and `False` on the second. `square`

This is the previous round's record/endpoint boundary one level down. There it
was: no record predicate detects steering. Here: **no record predicate detects
that the reasoner's own standards have drifted from what they answer to** — and
the conditions under test are record predicates by construction.

**SF-3. Classification.** Per the dispatch's four options, this is (4) with a
piece of (1), and **not** (3).

It is (4) — the target was underspecified — because `L*` has two readings and the
round separates them. On the **reasoner-relative** reading, where adequacy and
bearing are whatever the reasoner's current machinery says, the four conditions
are close to sufficient and the six counterexamples evaporate by construction. On
the **environment-relative** reading stated in `L_STAR.md`, they are refuted. The
dispatch's prose target is ambiguous between the two, and the ambiguity is not
cosmetic: it is the difference between a procedure that is internally consistent
and one that is answerable.

It is partly (1) — a condition was too weak — in one place: the previous round's
coverage compared the docket against a declared arrival list. Generation plus
entitlement plus a prospective read is strictly stronger and defeats attack D,
which the old form did not.

It is **not** (3), a missing fifth property, and SF-2 is why: the obstruction is a
measurability fact about the type of the conditions, not a gap in their content.

---

## 5. The fifth-condition attempt, and why disclosure beats prospectivity

**FC-1. Prospectivity refuses the positive control.** `WITNESS`. Under
prospectivity — a liability is judged by the adequacy in force when it was filed —
attack L's retroactive variant is refused, and so is attack K, the radical
legitimate transformation. The reason is exact: **adding a new way to settle a
demand is the same syntactic operation whether the new way is better or worse.**
A clause that refuses one refuses both.

**FC-2. Disclosure separates what prospectivity conflates.** `WITNESS`. Under
disclosure — a revision to the adequacy relation that reaches a live liability
must name that liability in the same edit — attack K is admitted and attack L's
retroactive variant is refused.

| | attack K (should pass) | attack L retroactive | attack L prospective |
|---|---|---|---|
| prospectivity | refused | refused | admitted |
| disclosure | admitted | refused | admitted |

**FC-3. Neither reaches the prospective variant.** `WITNESS`. Revise first, let
the demand arrive after, discharge under the new standard: nothing reaches
backwards, both clauses are satisfied, and `L*` still fails.

*Recommendation.* Disclosure, as a **recording requirement rather than a
prohibition**. It refuses nothing prospectivity would allow, it does not block
legitimate transformation, and what it buys is that standard drift is *in* the
record rather than inferable from it. That is the form a later judge — or a
counterfactual condition supplied from outside the record — can consume. It is
not a fifth conjunct of a sufficiency theorem, and this round does not offer one.

---

## 6. Independence

All six cells are witnessed, so the decomposition is not four labels kept for
symmetry:

| claim | witness |
|---|---|
| `P` without `I` | entitlement laundering |
| `I` without `P` | circular authorization |
| `RR + DA` without `P` | circular authorization |
| `P + RR + DA` without `I` | coverage flooding |
| `P + I + DA` without `RR` | an uncited coordinate move |
| `P + I + RR` without `DA` | a discharge with no backing |

**But the factorization is wrong at one place.** `I` is not atomic: it is
generation plus entitlement plus service, and *service obligations are
liabilities*, consumed by `DA`. Generation and entitlement are state coordinates,
so they are governed by `P` and `RR` like any other coordinate. The honest
architecture is therefore

    three conditions — P (what may be used), RR (how), DA (what is owed) —
    over a state whose coordinates include the machinery that generates and
    entitles inquiries.

`I` survives as the name of the requirement that service obligations be
discharged on time, which is a `DA` obligation with a deadline.

---

## 7. What the layer exports to deference

Unchanged in kind from the previous round and sharper in content. It exports: a
provenance-checked authority ancestry with `PR-1`; a branching-safe answerability
forest with `DA-2` and `DA-3`; and an explicit record of standard drift if
disclosure is adopted.

It does **not** export absence of manipulation, and now for two reasons rather
than one: the inherited non-recoverability result about influence, and `SF-2`
about standards. The deference layer must supply a counterfactual condition, and
the object it should attach to is the disclosed drift record, because that is the
only place the trajectory says its standards moved.

---

## 8. Open obligations

1. **Which scope discipline** — union or intersection — and whether the answer is
   a property of the constraint rather than of the provenance system (`PR-4`).
2. **A generative arrival process**. The environment declares demands; an advisor
   who controls what *arises* is still outside the model.
3. **Lean ports**: `PR-1` and `DA-2` are both short inductions.
4. **Whether the reasoner-relative reading is worth axiomatising** on its own, as
   an internal-consistency theorem with the four conditions close to sufficient.
5. **The disclosure record's interface** to a counterfactual condition.

## What is not established

No Lean; nothing registered. The environment is a modelling device and the round
does not claim such a structure is knowable. The finite models are one
substantive coordinate, at most six inquiries, horizons of at most three dates.
Attack J is recorded as a type mismatch rather than a defect: both arms of the
cost pair are licensed, so no predicate of either arm can express *why* one was
chosen, and selection is a fact about a policy's counterfactuals. The relation
between this round's boundary and the previous round's is stated as one shape
seen twice and is not proved to be one theorem.
