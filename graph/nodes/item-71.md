---
id: item-71
kind: leaf
leaf_kind: task
action: "Execute item 71 per its deliverable shape and acceptance check: Build the due-activation term in `roots()`."
who: agent
item: "71"
title: "Build the due-activation term in `roots()`"
section: "Normativity line — legitimacy"
maintainer_order: 47
difficulty: "open"
heading_notes: " — *specified, not built*"
project: normativity.legitimacy
dispatchable: true
item_status: open
deliverable: "the activation term, plus a verifier that recomputes rising edges from a shipped record and compares them against its roots."
acceptance: "a record in which no step is appended between two states and a claim nevertheless activates because the normative context changed; its negative, a resolved claim whose material stays represented and does not reactivate; and a recurrence, where a claim key falls and rises and mints a second root."
context: ["projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/ANSWERABILITY.md"]
author: "@smithy-verity"
size: M
size_reason: "one item entry of 341 words"
version: 1
---
## Statement
Item 71, Build the due-activation term in `roots()`, is delivered in the shape its entry states: the activation term, plus a verifier that recomputes rising edges from a shipped record and compares them against its roots.

## Source
PRIORITIES.md, item 71 (Build the due-activation term in `roots()`); its context: `projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/ANSWERABILITY.md`, *RI REALIZATION OF D1*; `COUNTERMODELS.md` §19.

## Notes
Transcribed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical); the entry's text is the Item section below, rendered back into PRIORITIES.md by checkers/priorities_render.py. The Statement is drawn from the entry's own deliverable line.

## Item
**Narrowed from a gap to an implementation task.** Legitimate Evolution needs the
conformance condition `D1`: every rising edge of `Due` must be realized by an
incurred claim. The seam in Reflective Integrity is now determined, and it uses
only functions that already exist.

```python
def active_due(self, t=None):            # Due supplied, as Permit is
    return self.due_sem(self.reasons(t), self.prestate(self._at(t)))

def new_due(self, t):
    prev = self.active_due(t - 1) if t > 0 else frozenset()
    return self.active_due(t) - prev

def roots(self, t=None):
    out = list(self.seed.roots0)
    for a in self.norm_events(t):
        out.extend(self.mint(a))
    for u in range(1, self._at(t) + 1):                    # the seam
        out.extend(self.mint_due(k, u) for k in self.new_due(u))
    return tuple(out)
```

`reasons(t)` already exposes the represented ledger as a prefix function,
`prestate` already exists, and `mint_ids` already keys ids by position so two
episodes of one claim key get distinct ids for free. **No new event kind.**

Three things to get right when building it. `Due` is a **level** and the edge is
taken against its own prior output, never against `roots` or `live` — otherwise
answerability decides what is owed. `D1` is an **inclusion**: carriage already
mints roots and must keep doing so. And because `roots` stays a pure function of
history, `D1` holds by construction in the semantic state; the conformance failure
lives at the boundary where a record is materialized or certified, so the check
belongs in whatever ships a record, as a recomputation.

Note the name collision to avoid: RI's existing `due(q,t)` means *this live root's
episode is being succeeded*, which is unrelated.

*Deliverable shape:* the activation term, plus a verifier that recomputes rising
edges from a shipped record and compares them against its roots.
*Acceptance check:* a record in which no step is appended between two states and a
claim nevertheless activates because the normative context changed; its negative,
a resolved claim whose material stays represented and does not reactivate; and a
recurrence, where a claim key falls and rises and mints a second root.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/ANSWERABILITY.md`,
*RI REALIZATION OF D1*; `COUNTERMODELS.md` §19.
*Reserved:* implementing it edits the Reflective Integrity Core round's artifact.
