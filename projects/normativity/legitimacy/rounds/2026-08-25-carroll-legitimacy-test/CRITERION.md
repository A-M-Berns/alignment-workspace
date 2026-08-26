# The criterion

Status: **proposal with a finite prosecution record; unregistered.** Class
`test-supported`. `src/legitimacy.py` is the implementation and
`tests/test_legitimacy.py` its mechanics; `MATRIX.txt` is the run.

---

## 1. Three questions, not one predicate

```text
prospective_license(case, I)      may the agent cause this intervention
legitimate_succession(case, a)    did this revision inherit its authority
current_standing(case, t)         which specifications are in force now
```

The source's question is which of a person's changing preferences should have
authority and legitimacy. In this round's vocabulary that question has no single
answer because it has no single subject: a preference is a reward
parameterization, authority is a relation a standing basis bears to an
intervention class, and legitimacy of an act is a prospective verdict. The
question decomposes because the parts of it come apart in constructed cases. `C4` has a specification in
force whose producing act was never licensed; `C7` has a licensed act producing a
parameterization no specification of which is in force. A single `Legitimate`
would have to answer both and would be wrong on one of them.

## 2. Prospective license

```text
ProspectivelyLicensed_t(I) :=
    exists b.  Authority_{t-1}(b, class(I))            live, covering, the
                                                       agent's, applicable
           and Independent(b, ancestry(episode(I)))    the counterfactual
    and no independent live authority prohibits class(I)
```

Three values, and a **ground** the status is a function of. The whole case
distinction:

| ground | when | status |
|---|---|---|
| `independent-permission` | an admissible independent permission covers the class, and nothing independent prohibits it | `Licensed` |
| `independent-prohibition` | an admissible independent prohibition covers the class, and nothing independent permits it | `Refused` |
| `conflict` | both | `Unresolved` |
| `defeated-citation` | a covering basis exists and none is admissible and independent — not live, not applicable, not the agent's, or not independent of the episode | `Unresolved` |
| `no-covering-basis` | nothing in the record covers the class | `Unresolved` |

**The permission language is not closed-world**, and this is the pass's second
repair. `Refused` is reserved for the one case where the record contains a
positive normative fact against the act. Under the closed-world reading the
first version had, a protocol saying *Alice may do C* refused Bob, a condition
that had not obtained refused everyone, and a lapsed permit prohibited what it
used to allow. None of the three is what those standings say, and each is now a
`defeated-citation`. `C29` runs one minimal case per ground and
`test_legitimacy.py` checks that `Refused` is reachable from exactly one of
them.

Independence is applied to prohibitions exactly as to permissions. An agent that
manufactures a prohibition to excuse inaction is doing what one that manufactures
a permission does, and the criterion has no reason to treat the polarities
asymmetrically.

**`Unresolved` is not permission.** The use rule is that an agent acts on
`Licensed` and on nothing else, so the two `Unresolved` grounds differ in what a
reader learns and not in what the agent may do. That is why the distinction sits
in `ground` and `defeated_citation` rather than in a fourth status: a status is
what an agent reads, and these two say the same thing to an agent.

## 3. The counterfactual

The anti-circularity condition is:

> An intervention may not acquire its sole prospective license by causing the
> normative state from which that license is issued.

Four questions had to be answered to state it.

**What is the counterfactual object?** Three versions died here.

`C10` kills *the single action*: the manipulation at `t0`, the authority it
produces at `t1`, and the intervention citing it at `t2` are three separate acts,
and removing only the third leaves the authority standing.

`C25` kills *one declared episode*: an agent that runs its campaign as two
episodes and cites the second keeps whatever the first installed.

`C27` kills *the walk from episode to episode*. Closing over "the episodes one
settlement-reference away, repeatedly" is not the same closure as "the episodes
reachable in the settlement graph", and a single unlabelled settlement between
the two halves of a campaign separates them. That was the implementation's actual
behaviour at the head this pass started from, and the manufactured permit came
back `Licensed`.

The object is the **ancestry class**, computed closure-first and projected
afterwards:

```text
AncSett(E)  = transitive predecessor closure in the settlement-reference graph,
              from the settlements belonging to E
ancestry(E) = { episode(s) : s in AncSett(E) } minus {none}, union {E}
```

`Settlement.refs` names *predecessors* — `WFStep(Settle)` refuses a settlement
whose references are not already on the ledger — so the graph is acyclic and the
closure terminates.

**What does removing it mean?** Replaying the record with the episode's
settlements gone. The replacement is an inert settlement rather than a deletion,
so every surviving step keeps its `tau` and every minted standing id is
unchanged — which is what makes "the same standing is still active" checkable by
identity rather than by resemblance.

**What descends from what?** Reflective Integrity decides, not this round. Only
the ancestry class's settlements are removed by declaration, at the level where the
vertical slice already puts authenticated interaction provenance. A reason citing
a removed settlement fails `WFStep(Reason)`; an event whose derivation cites that
reason fails `G2`; an event naming a standing that event would have created fails
`G4` or `G6`. Each falls in turn. In `C10` the declared removal is one settlement
and the surviving record contains no reasons and no events at all.

**What is independence?** The basis is independent when a standing with the same
id, the same payload and `Active` status is still there at the intervention's
strict pre-state in the excised record — **and** its applicability condition is
still discharged there. `C26` forced the second half: a seeded protocol survives
every excision, so an agent that cannot manufacture the authority can instead
manufacture the fact its condition reads. A protocol's condition is therefore
discharged from settled facts, which are inside the counterfactual, plus what the
case declares exogenous, which is not.

`C30` walks the boundary in five arms. A condition established only inside the
episode fails; one established only outside holds; one needing an exogenous fact
and an episodic one fails; one established outside and *also* restated inside
holds, because the outside settlement is still there in the excised record; and
one with two routes, of which the surviving route is exogenous, holds. The test
is that the condition is still discharged in the excised record, not that a
syntactically similar fact was present at some point.

An intervention with no episode has nothing to descend from, so every covering
basis is independent of it. That is the right answer rather than an exemption: a
rule that refused an act because it could not find an episode to blame would
refuse every ordinary act.

## 4. Succession

```text
LegitimateSuccession_t(x, x') :=
    the event that superseded x by x' is well-formed
    and the authority it named is independent of the episode
    and the event itself survives excision of the episode
```

**The third clause was forced by `C11`.** A person's own revision authority is
seeded, so it survives every excision; without the third clause a revision
reached entirely on manipulated grounds inherits it, and `C11`'s two trajectories
to the same cognitive endpoint receive the same verdict.
`authority_only_succession` is the version without it, kept in the module so the
two run side by side.

**The second clause is not redundant, and `C28` says exactly when it would be.**
It looks as though event survival should already imply it: an event that survives
excision passed `G4`, so the authority it names is an active `PAuth` in the
excised record. What `independent` asks in addition is that the payload be the
*same* one. A standing's payload is written once, by the event that creates it,
as `[[sigma]]_S (wit, PreState)` — and `S1`-`S6` permit that interpreter to read
the strict pre-state. So a minting event that survives excision can mint a
different authority.

`C28` runs both arms. Under a pre-state-reading minting schema the event survives
and the authority comes back carrying a different code, so the clauses disagree.
Under a pre-state-blind one they agree, and the argument that they must is short:
a standing id is `@s{tau}.{i}`, `tau` is preserved by excision, so the only event
that can mint that id is the one at that `tau`; if it survives with the same
witness and reads nothing else, the payload is identical, and if it does not
survive the id is absent and `G4` fails.

```text
every schema in the record is pre-state-blind
    ->  survives_excision(a, E) implies independent(schemaRef(a), E, tau(a))
```

Both clauses are kept because Reflective Integrity permits the schemas that
separate them, and the condition under which one could be dropped is now stated
rather than guessed at.

## 5. What the criterion is not

It is not the real-time objective: `C16` refuses what the real-time optimum
takes. It is not the constrained objective: `C18` licenses a policy outside the
constrained set. It is not temporal priority: `C10`'s laundering passes a
priority-only rule and is refused here. It is not actor identity: `C23`'s proxy
passes an author-matching rule and is refused here. It is not `RI.Good`: `C5`'s
record is `Good` throughout and the act is refused. It is not consent: `C7b`'s
basis is installed during the record by an ordinary licensed event, not seeded.

And it privileges no temporal index. `FinalApproval(I)` holds in `C4` and the act
is not licensed; `InitialDisapproval(I)` holds in `C8` and the act is licensed;
an initial standing is superseded in `C14` and a later request fails to supersede
one in `C13`.

## 6. What it does not do

**The excision operator has two properties one would want and does not get.**
`tests/test_excision.py` verifies determinism, position preservation,
admissibility of the result, subhistory-in-information, prefix causality,
idempotence and that excising nothing is the identity. It refutes monotonicity —
`E` a subset of `E2` does not give `Survivors(E2)` a subset of `Survivors(E)` —
and composition, which is not the excision of the union. Both fail on one
witness, `fixtures.nonmonotone_case`, whose schema is admissible exactly at an
even reason count: excising one episode leaves an odd count and the event falls,
excising both leaves zero and it stands. The witness is a legal Reflective
Integrity record. Both properties hold on every pre-state-blind fixture in the
round, which is the same lever as the succession clause above.

**It licenses nothing on a bare Carroll case.** Every one of the five examples,
with no enriched history, returns `Unresolved` — checked, in
`test_adversarial.py`. The criterion does not answer the source's question about
Bob and Diana; it says that the DR-MDP does not contain the answer and names what
would. Whether that is a result or an evasion is the honest open question of this
round, and the answer turns on whether records of the required shape are
obtainable, which nothing here shows.

**It reads a record counterfactual, not a world counterfactual.** Excision asks
what the record would have admitted, not what would have happened. A basis that
would have existed anyway — the person would have installed that protocol
regardless — is scored as dependent if the record's only path to it runs through
the episode. That is conservative in the direction of refusing, and it is a
genuine limitation rather than a design choice: nothing in the architecture
supplies the world counterfactual.

**Episode membership is an input, and provenance completeness is a hypothesis.**
Which settlements an episode caused is declared. `C23` shows why the declaration
sits at the settlement level rather than the actor level. `C25`'s second arm
shows the price: two episodes with no recorded reference between them are, as far
as the record can tell, causally unrelated, and a basis installed in the first is
scored independent of the second. The criterion is exactly as good as the
record's provenance links, and the hypothesis it needs is that every settlement
an episode caused refers to the settlement that caused it. Nothing here
establishes that any real record has that property.

**The supplied seam is wider than `covers`.** `covers` can only name a
structural edge of the DR-MDP, which is the protection the round claims for it.
A protocol's `condition` and the fact tokens a settlement establishes are opaque
strings the case supplies, and relabelling the DR-MDP renames neither — so `C3`
passing is not evidence that content cannot enter. It is one seam with three
fields, and `test_projection.py` says so rather than leaving the impression that
`covers` is the whole of it.

What `C31` settles is narrower, and is a negative result about widening: two
interventions sharing an intervention class, reachable from two different states,
are distinguished by the existing `condition` field without touching the class.
The action ontology was not widened, and nothing this pass built forced it.
