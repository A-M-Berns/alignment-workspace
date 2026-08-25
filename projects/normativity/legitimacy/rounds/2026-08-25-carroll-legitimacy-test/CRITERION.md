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

The source's question — which preferences have authority — decomposes because
the two halves of it come apart in constructed cases. `C4` has a specification in
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

Three-valued and never silently true:

| verdict | condition |
|---|---|
| `Licensed` | at least one admissible independent permitting basis, and no independent prohibition |
| `Refused` | a defeater — a covering basis that is not live, not applicable, not the agent's, or not independent; or an independent live prohibition |
| `Unresolved` | no covering basis at all, or two independent live authorities in conflict |

**`Unresolved` is not permission.** The use rule is that an agent acts on
`Licensed` and on nothing else. The distinction that earns the third value is
between a case with no relevant normative structure (`C6`, `C19`) and a case
whose structure defeats the act (`C10`, `C21`); collapsing them would make the
criterion say "forbidden" wherever it means "the record does not say".

## 3. The counterfactual

The anti-circularity condition is:

> An intervention may not acquire its sole prospective license by causing the
> normative state from which that license is issued.

Four questions had to be answered to state it.

**What is the counterfactual object?** Not the single action, and not one
declared episode either. `C10` kills the first: the manipulation at `t0`, the
authority it produces at `t1`, and the intervention citing it at `t2` are three
separate acts, and removing only the third leaves the authority standing. `C25`
kills the second: an agent that runs its campaign as two episodes and cites the
second keeps whatever the first installed. The object is the **ancestry class** —
the least set of episodes containing the intervention's own and closed under the
record's settlement references.

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

The third clause was forced. A person's own revision authority is seeded, so it
survives every excision; without the third clause a revision reached entirely on
manipulated grounds inherits it, and `C11`'s two trajectories to the same
cognitive endpoint receive the same verdict. `authority_only_succession` is the
version without it, kept in the module so the two can be run side by side.

The third clause needs no separate account of grounds: an event survives exactly
when its authority, its derivation's leaves and the standings it writes to are
all still there, which is the cascade already computed.

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

**`covers` is supplied.** `LEGITIMACY_LANGUAGE.md`'s last section is the same
gap seen from the language side.
