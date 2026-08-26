# Prosecution

Every version of the criterion the round built and rejected, with the fixture
that killed it, one rejected claim *about* the criterion's machinery, and one
implementation defect. Sixteen entries; **three** of the rejected rules are kept
in the source — `temporal_priority_license`, `author_matching_license` and
`authority_only_succession` — so those three comparisons run as tests rather than
sitting in prose.

Entries 4b and 5b were found by the hardening pass against the criterion as it
stood in this branch's earlier commits. Both were live: the ancestry walk
licensed a manufactured permit, and `Refused` was a closed-world reading of a
permission language. Entry 13 was found by the final pass and is not a defect in
the criterion — it is a claim the round made about excision that a legal record
refutes.

---

## 1. License by temporal priority

```text
Licensed_t(I)  :=  a live covering basis exists at t-1
```

Killed by `C10`. The manipulation at `t0` produces the authority at `t1`, and the
intervention at `t2` reads a basis that is genuinely earlier than it. Priority is
satisfied and the laundering succeeds. `legitimacy.temporal_priority_license`,
run beside the criterion in `test_adversarial.py`.

## 2. License by actor identity

```text
Licensed_t(I)  :=  the basis was not created by an event this agent authored
```

Killed by `C23`. Every event in the proxy fixture is authored by another actor,
so the rule finds nothing to attribute. It is also killed by `C10`, where the
authority-creating event is authored by the influenced person.
`fixtures.author_matching_license`.

## 3. Excision of the single action

The counterfactual removed the intervention and nothing else. Killed by `C10`
before it was written down: removing `t2` leaves `t1`'s authority in place.

## 4. Excision of one declared episode

Killed by `C25`, which the round built after the rest of the suite passed. The
agent runs `E1` and `E2`, manufactures its authority in `E1`, and declares the
intervention in `E2`. Removing `E2` leaves the authority.

The repair is the ancestry closure — the least set of episodes containing the
intervention's own and closed under the record's settlement references. It fixes
the linked arm and leaves the unlinked arm licensed, which is where the
provenance-completeness hypothesis of `CRITERION.md` §6 comes from. Both arms are
run and both results are asserted.

## 4b. Ancestry as a walk from episode to episode

The closure ran over episode labels: from the settlements of an included episode,
look one reference deep, and include whatever episode that reference belongs to.
Killed by `C27`, and this one was live at the head this hardening pass started
from — the manufactured permit came back `Licensed`.

```text
s2 in E2   ->refs->   s_mid in no episode   ->refs->   s1 in E1
```

An unlabelled settlement between the two halves of a campaign stops the walk. The
repair takes the transitive closure in the settlement-reference graph first and
projects to episodes afterwards, which is what the prose had claimed all along
and what the code did not do.

## 5. Independence of the standing alone

The basis had to survive excision; nothing looked at its applicability condition.
Killed by `C26`. A seeded protocol survives every excision by construction, so an
agent that cannot manufacture the authority manufactures the fact its condition
reads instead. The repair puts settled facts inside the counterfactual: a
condition is discharged from what the record still says obtains, plus what the
case declares exogenous.

## 5b. Closed-world permission

`Refused` was returned whenever no covering basis furnished a license: a permit
for another agent, a condition that had not obtained, a lapsed permit, a
manufactured one. Killed by inspection rather than by a fixture, which is why it
survived the first pass — every case in the suite only ever demanded *not
licensed*, so the over-broad value never showed up as a failure.

It is a closed-world reading of a permission language, and it makes the model
say three false things: that a protocol empowering Alice prohibits Bob, that an
unmet condition prohibits everyone, and that revoking a permit prohibits what it
used to allow. `Refused` is now reserved for an admissible independent
prohibition; everything else that is not a license is `Unresolved`, carrying a
`ground` that says which kind. `C29` is one minimal case per ground.

## 6. Succession by the authority it named

```text
LegitimateSuccession  :=  the PAuth the event named survives excision
```

Killed by `C11`. A person's own revision authority is seeded, so it survives every
excision, and a revision reached entirely on manipulated grounds inherits it. Both
arms of `C11` reach the same cognitive endpoint and the rule gives both the same
verdict. The repair requires the event itself to survive, which is the same
cascade rather than a new condition.
`legitimacy.authority_only_succession`, run beside the criterion.

## 7. A two-valued verdict

`Licensed` or `Refused`, with the absence of a basis counting as refusal. Rejected
before it was implemented, on three fixtures at once. `C6` and `C19` would report
"forbidden" where the record says nothing, and `C2`'s bare control would then pass
for the wrong reason — Bob and Diana equal because everything is refused, which is
the verdict a criterion that had learned nothing would also give. `C20` has no
place to put a conflict of two live authorities. The third value earns itself
three times over, and the cost of it is the use rule: `Unresolved` is not
permission.

## 8. Excision by deletion

Removing steps rather than replacing them with inert settlements. Rejected on
implementation: `tau` is assigned by `append` and minted standing ids are
`@s{tau}.{i}`, so deleting a step renumbers everything after it and "the same
standing is still active" stops being a statement one can check by identity.
`test_adversarial.py` pins that excision preserves the record's length.

## 9. Declared descent at every record level

The builder could have annotated every reason and event with the episode it
descends from. Rejected because the verdict would then be a function of the
fixture author's annotations rather than of the record. Descent is declared at
the settlement level only — where the vertical slice already puts authenticated
interaction provenance — and everything else falls by Reflective Integrity's own
admission rules. In `C10` the declared removal is one settlement and the excised
record contains no reasons and no events at all; the test asserts both.

## 10. Protocols covering content

A protocol whose `covers` named parameterizations by label — "this agent may make
this person energized". Rejected because `C3` and `C9` would then pass by
construction and fail as tests. `covers` holds index triples into the DR-MDP's own
declaration order, and `test_projection.py` checks that every entry is a triple of
integers.

## 11. Value standing as a commitment

Carrying a value specification as `PCmt` rather than `PValue`. Rejected for the
reason the vertical slice already gave: `PCmt`'s content is object-level, and a
projection that inspected it to tell a value specification from any other
commitment would read object-level content at meta level. `PValue` is imported
from that round rather than redefined.

## 12. A new historical event kind

An `InfluenceEvent` or an `EpisodeEvent` recording what the agent did. Not needed
and not added. The agent's acts reach the record as settlements, which is what a
raw interaction outcome already becomes, and the episode is a property of those
settlements. `test_language.py` checks that every step of every fixture in the
round is one of `Settle`, `Reason`, `Norm`, `Respond`.

## 13. Pre-state-blindness as the condition restoring the excision algebra

The hardening pass observed that monotonicity and composition held across every
pre-state-blind fixture in the round and wrote that pre-state-blindness was "the
lever" behind both failures. Killed by `C34`.

`fixtures.suspension_restoration_case` uses only pre-state-blind schemas: one
episode suspends an authority, another reactivates it, and a third event names it
where `G4` needs it `Active`. Excising the reactivating episode leaves the
suspension in place and the third event falls; excising both leaves the authority
never suspended and it stands. Monotonicity and composition both fail.

The repair is to the interpretation and not to the operator. There are two
independent sources of the failure — pre-state-sensitive schema interpretation,
and replay-sensitive admission itself — and only the first has anything to do
with blindness. The narrower `C28` result survives untouched, because it
quantifies over one excision and one surviving event rather than over two
excisions; `CRITERION.md` §4 carries its argument and the two are now stated
apart.

The attack was dispatched with a different mechanism in mind — removing a
stance-bearing standing so that a reason is disabled and an event citing it falls
under `G2`. That route does not work, and `fixtures.stance_restoration_case` is
the negative control: `G2` reads ledger membership of reason ids and
`WFStep(Reason)` reads settlement sources, so neither consults the stance set.
The proposed mechanism is blocked by the architecture's own "having a reason is
not taking a stance".

## 14. `relabel_case` dropping the settled-fact map

Not a version of the criterion — an implementation defect the hardening pass's
own honesty test found. `relabel_case` rebuilt a case without carrying
`fact_settlements`, so a relabelled case lost every fact its protocol conditions
read. `C3` passed anyway, because the case it relabelled discharges its condition
from `iv.facts` rather than from the record. The relabelling invariance was
therefore true and untested where it mattered. `C3` now relabels a second case
whose condition is discharged from a settled fact.

---

## What the prosecution did not achieve

**Five attacks were found that the criterion failed as then written**, and each
repair generalises rather than special-casing. Three came from the round's first
pass — `C25`, `C26` and the `C11` succession clause — and two from the hardening
pass, `C27` against the ancestry closure and the closed-world reading of
`Refused`. A sixth attack, `C34`, broke a claim the round made *about* the
criterion's machinery rather than the criterion itself. That is a weaker record
than it sounds: the suite is thirty-six rows the round wrote, and a criterion
built against them passing them is evidence about the round's imagination, not
about the criterion.

**Three of the six were in the gap between prose and code, or between a sample
and a claim.** `CRITERION.md` already said the ancestry closure was over
settlement references and the implementation walked episodes; `Unresolved` was
already documented as "the record does not say" and the implementation returned
`Refused` for four cases where the record does not say; and the claim that
pre-state-blindness bought the excision algebra was read off a sample of
legitimacy fixtures rather than off the admission rules. A round whose documents
and code are checked against each other only by the author has this failure mode,
and none of the three would have been found by running the suite.

**One attack is unresolved rather than defeated.** `C25`'s unlinked arm is
licensed. The round's position is that a record which does not link two episodes
of one campaign is a defective record and not a hard case, and the position is a
position rather than a result: nothing here shows that a real record could be
made to carry the links.

**The largest gap was attacked and stands.** Which structural class a protocol
covers is supplied by whoever builds the case, and the hardening pass widened the
statement of the gap rather than closing it: a protocol's `condition` and the
fact tokens a settlement establishes are also opaque supplied strings.
Relabelling the DR-MDP renames none of the three. `C31` establishes only the
narrow negative — that the existing `condition` field reaches a contextual
distinction the intervention class does not carry, so the action ontology did not
have to widen.
