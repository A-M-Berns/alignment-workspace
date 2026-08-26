# Answerability, activation, and the frozen Legitimate Evolution package

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

Grounded Replay is frozen and unchanged. The corrected Answerability Resolution
theorem, the A2 result, the asymmetric gating and the quantitative conclusions are
unchanged by this pass.

**One repair this pass.** The activation semantics memoized on claim content, so
a resolved claim could never recur. `Due` is now a **level** and what obliges is
its **rising edge**.

## DUE ACTIVATION SEMANTICS

```text
ClaimKey     an opaque label: what is owed, on this occasion
Ob(pos,slot) a claim occurrence: this claim, incurred here

ActiveDue_t  = Due(represented_{<=t}, L_t)        a level, supplied
NewDue_t     = ActiveDue_t \ ActiveDue_{t-1}      the rising edge
```

Each key in `NewDue_t` should be realized by an occurrence minted at `t`. Two
episodes of one kind share a key and are distinct occurrences.

**Transition order.** One phase structure, and both semantic reads take the
strict pre-state:

```text
(L_t, O_t)                          strict pre-state
  represent event t's material      descriptive, from the current event
  ActiveDue_t = Due(reasons_{<=t}, L_t)
  NewDue_t -> incur                 ungated
  Resolve judged at (L_t, O_t)      gated
  accepted normative effect -> L_{t+1}
  O_{t+1} = (O_t u opens_t) \ (disch_t u moved_t)   if accepted
```

Descriptive material from the current event; normative standing from the strict
pre-state. That is the mix §7 of the dispatch asked for, and it is why an
unauthorized act's own occurrence can activate a complaint at its own position
while a self-authorizing act cannot license its own resolution.

## RI REALIZATION OF D1

**Exact current gap.** Verified again against
`rounds/2026-08-24-reflective-integrity-core/src/ri_core.py`:

```text
roots(t)     = seed.roots0 + [mint(a) for a in norm_events(t)]
mint(a: NormEvent)  -> Transfer: one root (eff.x, eff.to)
                    -> otherwise: one per fresh_n(ctx, eff), debtor a.author
reasons(t)   = tuple(s.e for s in steps[:t] if isinstance(s, Reason))
prestate(tau)
responses(t) = tuple(s.rho for s in steps[:t] if isinstance(s, Respond))
closed(q,t)  = q.demand.run(q, responses_for(q,t), ...)
due(q,t)     = live(q,t) and any(disposes(a,q) for a in norm_events(t))
```

`roots` never consults `reasons`. That is the whole gap.

**Exact smallest repair.** Option **B**, a derived projection, using only
functions that already exist:

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

**No new event kind.** `Reason` already exists as a step, `reasons(t)` already
exposes the ledger as a prefix function, `prestate` already exists, and
`mint_ids` already keys ids by position so two episodes of one key get distinct
ids for free.

**Stored, derived, or both: derived.** `roots` is already a pure function of the
history, and adding an activation term keeps it one. Note honestly what that
does: in the **semantic** state D1 then holds by construction. It does not
thereby vanish — it relocates to the boundary where a record is materialized or
certified, and that is where a conformance check belongs. The three levels:

```text
semantic RI state       derived; D1 holds by construction
materialized record     a stored root list that can omit a derived root
external certificate    what a consumer actually receives
```

**What an external verifier checks.** Replay `Due` over the represented state and
compare its rising edges against the claims the record incurred. Concretely: for
each `t`, recompute `ActiveDue_t`, take the edge, and check each key in it is
realized by a root minted at `t`.

This is a **recomputation, not an inspection**, and it has to be, because the
omission is invisible structurally. `TestTheVerifierTest` runs exactly that
comparison on the three broken constitutions: Grounded Replay clean, A1 clean,
Answerability Resolution clean, no-silent-loss clean, D1 fires. Nothing about the
recorded roots is wrong. What is wrong is which roots exist.

**What the verifier needs out of band:** `Due`. Exactly as it already needs
`Permit` to replay standing. Two parties with different `Due` semantics disagree
about what was owed, and nothing in the record settles it. That is a real
residual and it is the same residual the architecture already carries for
`Permit`; it is not a new hole opened by this pass.

**Old reason newly due** works because `Due` reads `(reasons_{<=t}, L_t)` and
`L_t` changes. **Recurrence** works because the edge is on a level, so a key that
falls and rises again mints a second root at the second rise. **Same-step
resolution** works because `Respond` is already independent of `NormEvent`, so a
root minted at `t` can be closed by a response at `t` without ever being live in a
visible state — and RI already exposes that through `closed`.

## FROZEN LEGITIMATE-EVOLUTION PACKAGE

```text
STATE
  L_t  standing occurrences        Occ(pos, slot)
  I_t  incurred claims             Ob(pos, slot),  never shrinks
  O_t  outstanding claims          O_t subset I_t

LOCAL SEMANTICS  (opaque, supplied)
  Permit   may this event change standing, at the strict pre-state
  Due      a level over the represented state and the strict pre-state
  Resolve  done, or carry(S), judged at the strict pre-state

STRUCTURAL PREMISES
  S1  grounds(e_t) subset { o in L_t : Auth(o) }
  S2  apply_t(L_t,e_t) != L_t  ->  grounds(e_t) != {}
  A1  a claim leaves O only by Resolve: done, or carry(S) with S non-empty
      and S subset O_{t+1}

REALIZATION CONFORMANCE
  D1  NewDue_t subset NewlyIncurred_t          inclusion, not equality

STRUCTURAL CLOSURE
  Grounded Replay          every admitted occurrence has a finite grounding
                           tree, leaves in G, positions strictly descending
  Answerability Resolution every incurred claim has a finite resolution
                           derivation, frontier non-empty, every branch
                           outstanding or discharged

GLOBAL LEGITIMATE EVOLUTION  (the composition)
  every live standing has legitimate ancestry to the accepted base, and
  every claim the process's own semantics newly made due has a complete
  resolution derivation ending only in legitimate discharge or the current
  outstanding frontier

GATING
  standing change   Permit          incurrence  ungated       resolution  Permit

OUTSIDE
  Coverage, progress, regret, substantive correctness, quantitative liability,
  current-state certification
```

### Whiteboard

```text
Incurred never shrinks; Outstanding is incurred-minus-resolved.
Due is a level; its rising edge is what obliges. Falling edges resolve nothing.
Claims arrive ungated (even from refused acts); they leave only by Resolve at
the strict pre-state, into a nonempty successor set still outstanding after.
Theorem: every incurred claim has a finite resolution tree, all leaves open or
discharged. D1 (conformance, checked by recomputation) makes that cover
everything Due activated.
```

## 1. The repair: a level, not a memo

The previous version computed newness by memoizing claim content: a key once
incurred was never newly due again. That gets persistence right and recurrence
catastrophically wrong. Build a lapse, fix it, and have it happen again:

```text
active   at 0, 1        incurred q:lapse-1, discharged at 1
inactive at 2
active   at 3           a second, genuine episode
```

Memoization reports no activation at `3`, so a process that ignores the second
lapse entirely satisfies D1. The failure is silent and total: the model could not
express a recurring obligation at all.

The rising edge fixes both at once.

```text
                     no reopening   recurrence   non-circular
persistent predicate      no            yes          yes
memoize on content        yes           no           no
rising edge on a level    yes           yes          yes
```

The third column matters and is easy to miss. Memoizing consults `Incurred` —
answerability state deciding what is owed, which is the circularity §16 warns
about. The rising edge consults `ActiveDue_{t-1}`, which is `Due`'s own previous
output. That is bookkeeping over the semantics' decisions, not the answerability
state feeding back into them.

**A falling edge resolves nothing.** `falling_edge_is_not_resolution` incurs a
claim and then goes quiet; the claim stays outstanding. What stops being owed is
decided by `Resolve`, never by the reasons ceasing to be represented.

## 2. Activation identity, and its boundary

`Due` returns keys that already individuate the occasion. The structure mints the
occurrence. So a key is *what is owed on this occasion*, and an `Ob` is *the
occasion's record*.

Two levels, and both earn their place: `Due` speaks about keys, the resolution
theorem speaks about occurrences, and recurrence needs one key to have several
occurrences. `office.Constitution.claim_keys` is where a fixture says two
obligations realize one key.

The boundary worth stating: two genuinely independent claims of the same kind,
simultaneously active and indistinguishable in the represented state, are one key
and therefore one claim. That is not a defect being hidden. If the represented
state cannot tell them apart, neither the process nor a verifier can, and
inventing a distinction would be inventing content.

## 3. Inclusion, not equality

`D1` is `NewDue_t subset NewlyIncurred_t`. Equality would say `Due` is the
complete genesis semantics for answerability, and it is not:
`succession_incurs_without_due` carries a claim to a successor, which incurs an
occurrence that `Due` never activates. Requiring equality would refuse ordinary
succession.

So there are exactly two legitimate geneses: activation, and carriage. RI has the
same two — `mint` on a `Transfer` is carriage, and the seam adds activation.

## 4. The verifier test, and where D1 belongs

`recurrence_ignored` is the case that settles it. Every recorded root has perfect
continuity; Grounded Replay, A1, the resolution theorem and no-silent-loss are all
clean; and the second lapse was never taken on. No structural check catches it,
because nothing structural is wrong — the record is internally impeccable and
incomplete.

The only thing that catches it is recomputing the activation and comparing. That
is the practical criterion the dispatch asked for, and it is what puts `D1` at the
realization boundary rather than among the premises: a premise is discharged by
construction, a conformance condition is checked against a record.

## 5. Every layer owns a distinct failure

```text
Permit failure          illegitimate standing          S1/S2, Grounded Replay
Due-conformance failure an owed claim omitted          D1, by recomputation
Resolve failure         an owed claim erased           A1, Answerability Resolution
Coverage failure        a reason never represented     outside; not a defect here
Regret failure          exposed repair ignored         outside; downstream
```

Each row has an executed witness and none of them is caught by another row's
check. That separation is the reason to call the package frozen rather than the
absence of remaining questions.

## 6. Provenance adequacy

`Due` is only as good as its supplied represented state. That is not Coverage.
Coverage asks whether relevant external failures reach the represented state at
all; this pass assumes an adequate descriptive view exactly as the rest of the
round does, and inherits the unsolved provenance-completeness assumption
unchanged.

## 7. What no claim above asserts

- No claim that the RI seam is implemented. It is specified down to the function
  and not built; building it edits a previous round's artifact.
- No claim that any claim is ever discharged, or that anything ought to have been
  represented.
- No claim that `Due`'s activation form is uniquely minimal — only that
  persistence, arrival-minting and content-memoization are each refuted by an
  executed countermodel.
- No claim that two parties with different `Due` semantics can be reconciled by
  the record. They cannot, and the same is already true of `Permit`.
- No claim that a conforming process is good. `high_regret` conforms.
