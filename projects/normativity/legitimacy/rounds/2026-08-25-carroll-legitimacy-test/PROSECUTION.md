# Prosecution

Every version of the criterion the round built and rejected, with the fixture
that killed it. Four of the rejected rules are kept in the source, so the
comparison is a test rather than a memory.

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

## 5. Independence of the standing alone

The basis had to survive excision; nothing looked at its applicability condition.
Killed by `C26`. A seeded protocol survives every excision by construction, so an
agent that cannot manufacture the authority manufactures the fact its condition
reads instead. The repair puts settled facts inside the counterfactual: a
condition is discharged from what the record still says obtains, plus what the
case declares exogenous.

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

---

## What the prosecution did not achieve

**No attack was found that the surviving criterion fails outright.** Two were
found that it failed as then written, and both produced repairs that generalise
rather than clauses that special-case. That is a weaker result than it sounds:
the suite is twenty-eight fixtures the round wrote, and a criterion built against
them passing them is evidence about the round's imagination, not about the
criterion.

**One attack is unresolved rather than defeated.** `C25`'s unlinked arm is
licensed. The round's position is that a record which does not link two episodes
of one campaign is a defective record and not a hard case, and the position is a
position rather than a result: nothing here shows that a real record could be
made to carry the links.

**The largest gap was not attacked at all.** Which structural class a protocol
covers is supplied by whoever builds the case. Every fixture in this round picks
that class honestly, and nothing in the model would notice if one did not.
