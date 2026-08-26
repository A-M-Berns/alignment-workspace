# Proper Exercise

Status: **prosecution record and a negative result; unregistered.** Names
provisional under `AGENTS.md` §6. Nothing is Lean-checked and no claim is
registered. Grounded Replay is unchanged by this pass.

---

## MINIMAL PROPER-EXERCISE KERNEL

**The question.** Grounded Replay says an authority has legitimate ancestry. It
says nothing against a fiscal authority legislating on safety.

**Types.** Nothing new in the kernel. Over it, supplied by the semantics:

```text
Cap   : Content -> Pfin Scope          what an authority may license
Reach(L) = union { Cap(content(o)) : o in L, Auth(o) }
```

**The local judgment.** Already present, and this pass found no reason to
restructure it:

```text
Valid(L, e)  :=  grounds(e) subset { o in L : Auth(o) }        S1, hereditary
             and (changes(L,e) -> grounds(e) != {})            S2, hereditary
             and ProvComplete(e)                               local
             and Permit(L, e, ProvView(e))                     local
```

**Hereditary versus local.** `grounds(e)` is hereditary — the grounding tree
recurses through it. `ProvView(e)`, the state `L`, and everything `Permit` reads
about either are **local**: consulted at the judgment, never ancestors. A live
veto that refuses an act appears in no tree, and neither does a persuading
argument.

**Grounds live on the edit, not on a witness.** So the invoked basis is part of
the act, an act invoking a different basis is a different act at a different
position, and proof-relevance buys nothing: the route is determined by the edit.

**Results.**

| | statement | status |
|---|---|---|
| **E1** | Reach changes only at an accepted edit | theorem, and a restatement of the replay |
| **E2** | No edit's permission can rest on a capability it creates | **theorem**, quantified over all `Cap`, from strict pre-state evaluation plus freshness |
| **E3** | The capability an act confers is *available* to the permission | true by the effect being inside the edit — **and not a theorem that it is checked** |
| **E4** | If no accepted edit widens beyond its basis, `Reach` is non-increasing | **theorem about a class of `Permit`s**, and the hypothesis is declinable |

**One countermodel per claim.**

| | drop it | what happens |
|---|---|---|
| E2 | let an act cite the rule it creates | `self_amendment(False)`: the ground is in `issue_t`, the pre-state lacks it, the act is refused — so E2 is not vacuous |
| E3 | let permission not read what is issued | `blind_permit`: **the same gazette** as `self_expansion`, same kernel verdicts, and it escalates |
| E4 | let a constitution license widening | `constitutional_widening`: reach gains a scope, legitimately |

**Do authority-transforming edits need special structure?** No. They are ordinary
edits whose issued content happens to be an authority. Self-amendment,
delegation and total constitutional replacement are all one calculus, and the
distinction between them is a fact about `Permit`, not about the edit type.

**Does privilege escalation have a clean mathematical definition?** Yes:
`Reach(L_{t+1}) \ Reach(L_t) != {}` at an accepted edit that widens beyond its
basis. It is clean, it is checkable, and **no theorem rules it out**, because
`blind_permit` differs from a refused act only in the semantics.

**What Reflective Integrity is missing.** `PAuth` carries a `SchemaCode` and no
capability, so `Cap` is empty on it and E4's hypothesis is vacuous on a record.
`PProto`'s `covers` is a capability but there is **no slot in a `NormEvent` for
citing a governing protocol** — `schemaRef` names a `PAuth` and `steps` name
`PAuth`s. So an external-rule discipline is *not* sufficient without a type
change: RI needs either a capability field on authority-bearing standing or a
place for an event to cite one. `PRIORITIES.md` item 67.

---

## 1. The separations

Fourteen, all executed. Each is a constitution and its gazette, and every one
satisfies the kernel's premises — the kernel never distinguishes them.

```text
A  fiscal authority, fiscal edit                       accepted
B  the same authority, safety edit                     refused
C  safety authority delegates narrower                 accepted
   delegates equal                                     accepted
D  delegates broader                                   refused
   delegates incomparable                              refused
E  ordinary authority expands itself                   refused
F  amendment authority widens another office           accepted
G  the amendment rule amends itself, under the old rule accepted
   the same act citing the rule it creates             refused
   total constitutional replacement                    accepted
   two-of-three board                                  accepted
   one-of-three board                                  refused
   an act invoking a basis that does not authorize it  refused
```

## 2. What `Permit` turned out to need

Nothing structural. `Permit(L, e, r)` with `grounds(e)` on the edit already
handles every case above:

**Joint and threshold authority** — the edit names the members it invoked and the
predicate counts them. No authority algebra; `replay.py` contains no occurrence
of *quorum*, *threshold* or *vote*, and the check reads the module to say so.

**Negative side conditions** — `Permit` reads the state, so a live veto refuses
an act without becoming one of its ancestors.

**Content sensitivity** — a live policy may ban a scope. This is why content
invariance stayed withdrawn.

**Authority over authority** — a token in the acting basis's own capability
vocabulary. The kernel does not know it exists.

## 3. Ex-post rationalisation

`ex_post_rationalisation`: an act invokes a fiscal warrant for a safety measure
while a safety warrant sits live and unused beside it.

```text
exists B. Permit(L, B, r, e)     would accept it
the act's own grounds            do not authorize it
```

The act is refused, and it stays refused: invoking the other basis would be a
different act, at a different position, issuing different occurrences. So
legitimacy is tied to the **actual exercise route**, and that follows from
grounds living on the edit rather than being existentially quantified.

The round therefore does **not** need a proof-relevant `ProperExercise` witness.
The prompt asked whether the important object is `pi : ProperExercise(L,e)` with
accessible support. It is not, because the support is already in `e`.

## 4. Why there is no no-escalation theorem

The decisive pairing:

```text
self_expansion   base { fiscal }   act issues fiscal|safety   refused
blind_permit     base { fiscal }   the same act              accepted, reach grows
```

Same base, same edit — same grounds, same disposals, same issued content, same
declared evidence. Both satisfy S1 and S2, both satisfy the grounding theorem,
both satisfy no-self-ratification and persistence. The only difference is that
one constitution's `Permit` reads the issued capability and the other's does not.

So any theorem of the form *"proper transitions imply no unauthorized privilege
escalation"* must quantify over `Permit`, and no such quantified statement is
true. What is true is the conditional E4, whose hypothesis is a property of
`Permit` — and a constitution that means to allow amendment declines it on
purpose.

**Escalation is only measurable against a base that is not plenary.** With a
plenary charter live, `Reach` is already everything and no act can grow it. That
is why the escalation fixtures use narrow bases, and it is a modelling fact worth
recording rather than a trick.

## 5. What this changes about Grounded Replay

Nothing. The kernel does not import this module, has no capability notion, and
its premises hold on every constitution here including the escalating one. Proper
Exercise decorates each accepted edge with a local judgment; it does not extend
the replay.

The stronger lineage statement the prompt anticipated — *every internal edge
carries a proper-exercise witness* — is available and is not worth a name: the
witness is the acceptance of the edit, which the tree already records.

## 6. What this pass does not establish

That `Permit` cannot be given useful structure for *some* purpose. It establishes
that no structure was needed for the fourteen separations, and that the natural
candidate constraint — capability monotonicity under delegation — is refuted by
constitutional widening.

Anything about reasons, liability or deference. Reasons appear only as local
evidence and the round did not formulate defeat, due-ness or response
obligations.

That the office model's `Cap` is the right capability language. Scope tokens with
subset containment were enough to separate fourteen cases; nothing here says a
real jurisdiction is a set of tokens.
