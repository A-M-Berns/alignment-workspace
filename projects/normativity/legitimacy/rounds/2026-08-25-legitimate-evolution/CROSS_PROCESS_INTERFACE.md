# What one process receives, and what it may infer

Status: **specification; unregistered.** Names provisional.
`LEGITIMATE_EVOLUTION.md` carries the theorem.

---

## 1. Three questions, not one

The previous interface offered a grounding tree as "essentially the whole
certificate". It is not. Three questions come apart and only the first has a
finite certificate:

```text
origin          was this occurrence legitimately issued?     a grounding tree
historical      what has happened to it since?               the accepted disposals
current         is it in force now?                           the replay
```

`office.lineage_versus_current` is where they separate: an authority validly
issued, validly used, validly revoked. Its tree is intact and it is not live. A
tree is built from grounds; disposals are not grounds; so a tree **structurally
cannot** answer the third question.

## 2. What a tree gives

```text
Recognizes_A(G)  and  A accepts (Auth, Valid)  and  pi is a tree for o
------------------------------------------------------------------
A may conclude:   o was legitimately issued
A may not conclude:   o is in force
```

The tree is finite in the size of `o`'s ancestry, its leaves are in the base, and
its internal nodes are edits `A` can check. That is the cheap part and it is
genuinely cheap.

## 3. What a current-state claim costs

It is history-sensitive and there is no way around that. To know `o ∈ L_t`, `A`
needs to know that no accepted edit in `(s, t]` disposed `o`, and *accepted* is
itself a replay judgment. So one of:

1. **`A` replays the prefix.** Needs the trace and `Valid`, and gives the exact
   answer.
2. **`B` commits to a state and proves the delta.** Needs a commitment scheme and
   a proof that the edits since it were applied correctly; nothing here builds
   one.
3. **`A` accepts an attestation of currentness**, which is a trust assumption and
   should be recorded as one.

The previous interface offered route 1 without saying so, because its certificate
had a currentness check hidden inside it.

## 4. Checkers, and what a recognizer must require

If `A` does not evaluate `Valid` itself but uses a checker, the condition is
**agreement along the trace**, not soundness:

```text
for every t:   Check(L_t, e_t)  <->  Valid(L_t, e_t)
```

One-sided soundness is worth nothing. A checker that misses a valid revocation
keeps an authority the semantics removed, and `A` then positively recognizes an
authority that is no longer legitimate — `COUNTERMODELS.md` §3. This is a change
from the previous pass, which said soundness sufficed for recognition and was
wrong.

Both consumers need the same condition, so the earlier asymmetry between them is
withdrawn too.

## 5. What A must be told

```text
G          the base                    A recognizes it or the question is empty
Auth       which occurrences may ground an edit
Valid      the semantic relation, or the pieces that define it
alpha      the audit context — what is believed about the past
```

`alpha` is not a formality. Two recognizers with the same base and the same
semantics can legitimately disagree about what is in force, because they believe
different things about whether an old edit's conditions were met. Recognition is
indexed, not absolute.

## 6. The recognition axiom

Unchanged in status and narrower in what it commits to:

> **(R)** `A` regards an occurrence admitted by the replay of a process whose
> base, authority predicate and validity relation `A` accepts, at an audit context
> `A` accepts, as one it recognizes. `[AXM]`

The mathematics does not derive it. What it does is say exactly what (R) is a
commitment to — S1, S2, and the semantics `A` accepted — and exactly what it is
not: it says nothing about what the occurrence's content is, and nothing about
whether the occurrence is still in force.

## 7. The three interfaces

```text
legitimate    entitled                  o in Adm, or o in L_t
accountable   answerable                not in this object
serviceable   sustainably enforceable   not in this object
```

Independent, and the kernel carries no field for either of the others. Custody —
who is answerable — is not in the state at all, so a `Transfer` in a record is a
no-op on `L`.
