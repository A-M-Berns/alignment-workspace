# Legitimate evolution

Status: **specification and reference models; unregistered.** All names are
provisional under `AGENTS.md` §6. The statements are paper derivations, each
exercised by finite processes in `src/` and `tests/`; nothing is Lean-checked and
no claim is registered. `test-supported` is the ceiling.

Tags: `[DEF]` true by the type · `[THM]` derived · `[ASM]` a hypothesis on a
parameter · `[AXM]` a substantive input the mathematics does not supply.

---

## 1. The object

The legitimate state is **reconstructed**, not filtered out of what a process
happens to be doing.

```text
L(alpha, 0)    = G
L(alpha, s+1)  = apply(L(alpha, s), e_s)   if Valid_alpha(L(alpha, s), e_s)
                 L(alpha, s)               otherwise
```

A process proposes a finite sequence of frozen **edits**. What it actually does
with them is a fact about the process. What is legitimately in force is `L`.

The two indices are independent and both are needed. `s` is historical time —
when the act was performed. `alpha` is the audit context — what is currently
believed about the past. Changing `s` is normative revision; changing `alpha` is
a revised assessment of a revision that already happened, and conflating them
loses one of the two.

```text
                the interface: Occ, Edit, G, Valid, Permit, ProvOK, Xi, alpha
                          |
                          |   H1-H6  ==>  G1-G6
                          v
   a legitimate state, and two projections of it
  ------------------------- realization boundary -------------------------
   Reflective Integrity, standing folds, reason provenance, episodes
                          |
                          |   realization theorem
                          v
                 proposes an edit sequence satisfying H1-H4
```

`src/replay.py` names no normative event, reason occurrence, settlement,
answerability root, price or replay of a record; `tests/test_replay.py` checks
that by reading it. `src/office.py` builds processes from a constitution and its
gazette and imports `replay` and nothing else of this repository's.

## 2. Occurrences, not contents

```text
Occ  = (at, index, sort)      what a particular act put in force
```

An occurrence is *this* grant, tagged by the index of the edit that issued it.
Two acts proposing the same policy propose two occurrences.

This is the load-bearing ontological choice and it earns three things at once.
Freshness is free — an edit cannot issue an occurrence tagged with anybody
else's index — so **unique issuance is not an axiom and the question the previous
pass argued about does not arise**. No-laundering becomes true. And a later clean
act can adopt the very content a rejected act proposed, because content is not
what is being tracked.

`sort` is `authority` or `norm`. It is the least structure that lets one
legitimate state serve two consumers, and the frame never reads what an
occurrence *says*.

## 3. The edit

```text
Edit = ( at, grounds, dispose, issue, input, exercise, scope, request )

grounds   B   the occurrences invoked as the authority for this act
input     I   the authorization-relevant information declared for it
exercise  X   the evidence that this was an authentic exercise
request       what the act asked for
dispose       what it ended
issue         (sort, content) per occurrence it put in force
scope         the domain it purports to act in
```

```text
declared(e) = (grounds, input, exercise, scope, request)
apply(L, e) = (L \ dispose(e)) union issued(e)
```

`declared(e)` is what a legitimacy judgment may read; `dispose` and `issue` are
what the act turned out to do. Keeping them apart is what gives the factorization
hypothesis content — *same declared view, same effect* is then a claim, and it is
false of a realization whose effect reads state nobody declared.

## 4. The hypotheses

**H1 — mediated mutation.** The legitimate state changes only by applying an
edit. *Nothing comes into or out of force except by an act on the record.*
Architectural. `[DEF]`

**H2 — fresh occurrence.** An edit issues occurrences nobody has issued and
nothing holds. *A grant is a new thing, not a re-entry of an old one.* Free from
the type. `[DEF]`

**H3 — strict-prestate grounding.** `Valid_alpha(L, e) => grounds(e) ⊆ Auth(L)`.
*You act under authority you already have.* `[ASM]`

**H4 — permit soundness.** `Valid_alpha(L, e) => Permit(L, grounds(e), input(e), e)`.
*Holding a warrant is not doing whatever you like with it.* Jurisdiction, scope,
consent conditions, amendment rules and procedural conditions live in `Permit`,
which is a parameter: the interface requires that some such relation be
consulted, not what it says. `[ASM]`

**H5 — declared factorization.** Two proposals with the same declared view have
the same verdicts and the same effects. *Whatever the legitimacy rules read, they
read through the interface.* `[ASM]`

**H6 — threat-relative provenance adequacy.**
`Valid_alpha(L, e) => ProvOK_alpha(e)`, and every influence in `Xi` is one
`ProvOK` can refuse. `ProvOK` splits into `InputOK(I)` — is the declared
information authentic — and `ExerciseOK(e, X)` — was this an authentic exercise.
`[AXM]` for the adequacy half: `depends` is a fact about the world and nothing
here computes it.

**`Valid` is a parameter and none of the theorems assumes it is any good.** What
they assume is H1-H6, and each is a condition a realization can fail. The
substantive normative content of legitimacy sits entirely in `Permit` and
`ProvOK`; what is proved below is structural.

## 5. The theorems

**G1 — finite grounding.** Every legitimate occurrence has a finite grounding
tree: leaves in `G`, internal nodes accepted edits, children the grounds that
edit invoked, and the historical index strictly decreasing downwards.

*Proof.* Induction on the historical index. The base holds at `L(alpha,0) = G`.
An accepted edit at `s` has `grounds ⊆ Auth(L(alpha,s))` by **H3**, and by **H2**
every occurrence of `L(alpha,s)` was issued strictly before `s` or lies in `G`;
so each ground has a tree of strictly smaller index, and hanging them under `s`
gives one for what `s` issued. ∎ `[THM]`

Not an unfolding: drop **H3** and an edit grounded in an occurrence nobody issued
is applied, and what it issues has no tree at all.
`TestTheCompressionIsNotDefinitional` runs both sides.

**G2 — no self-ratification.** No accepted edit is grounded in what it issues. By
**H3** its grounds are in the pre-state; by **H2** what it issues is not. `[THM]`

**G3 — no laundering.** An occurrence a rejected edit proposed never becomes
legitimate.

```text
not Valid_alpha(L(alpha,s), e_s)  =>  for all u > s,
    no occurrence e_s proposed lies in L(alpha, u)
```

*Proof.* The rejected edit is a no-op, so its occurrences are absent at `s+1`;
by **H2** every later edit issues occurrences tagged with its own later index, so
none of them is one of these. Downstream use cannot help: a later edit invoking a
rejected occurrence as a ground fails **H3**. ∎ `[THM]`

The work is done by the ontology rather than by the induction, and that is the
argument for the ontology. `office.laundering` uses a doubted grant three times
and never rehabilitates it; `office.readoption` adopts the same content by a
clean act and is legitimate.

**G4 — hidden-state noninterference.**

```text
View_alpha(P) = View_alpha(P')   =>   L(alpha, t)(P) = L(alpha, t)(P')
```

*Proof.* Induction on the step from **H5**: the declared view determines the edit
and the verdict, and the state at each step is a function of the previous state
and those. ∎ `[THM]`

Raw histories may differ arbitrarily outside the declared view. Authorized
influence is not excluded — an influence that changes the declared input changes
the view, and the two sides are then permitted to differ.

**G5 — persistence until a valid edit changes it.**

```text
o in L(alpha, s)  and no accepted edit in (s, u] disposes o
    =>  o in L(alpha, u)
```

A rejected edit is a no-op and an accepted edit that does not dispose `o` keeps
it. `[THM]`

This is the property the previous formulation did not have. It took the raw
lifecycle and intersected it with a derivability set, so an occurrence left
whenever *anything* removed it — including an act with no legitimate authority at
all.

**G6 — unrestricted permitted revision.** Relabelling what occurrences say
changes nothing legitimate. `apply` reads no content and `Occ` carries none.
`[DEF]`, and a falsifiable condition on a realization.

## 6. Audit contexts, and the surprise in them

**Retraction.** Tightening `alpha` can invalidate a historical edit and
everything grounded in what it issued. `office.audit_discovery`: under
`alpha:trusting` an appointment and the norm made under it are legitimate; under
`alpha:informed` the appointment's finding is doubted and both fall. **No
historical rule changed** — only what is believed about whether it was satisfied.

**Restoration, and it is not a defect.** Tightening `alpha` can put *more* in
force. `office.audit_restores`: the invalidated edit was a repeal, so
invalidating it leaves its target standing.

So `L` is not monotone in the audit context in either direction. The previous
branch met this as the challenge operator being neither monotone nor composable
and could only record it; here it has a one-line explanation, which is the clearest
single sign that the object was wrong before.

## 7. What is no longer in the theory

**Challenge survival.** `q |= t`, `Chal`, issuance stability and origin necessity
are gone from the headline. The judgment is now local: *did prior legitimate
authority permit this exact edit, given this declared input?* Carroll-style
excision realizes `ProvOK` and is one way to compute it.

That is a strict improvement in two directions and a named cost in a third.

*It refuses less.* An edit that would not have happened but for an argument was
scored dependent on that argument. `office.persuasion` is the case: Alice revises
after Bob's argument, removing the argument removes the edit, and the edit is
legitimate. The old criterion counted this against it — the Carroll round called
itself "conservative in the direction of refusing" and this is where that bit.

*It refuses better.* Jurisdiction is now expressible. `office.unauthorized_scope`
is a warrant with impeccable grounds and impeccable provenance used outside its
domain, and the previous calculus admitted it because it checked that the licence
was derivable and never what the licence was *for*.

*The cost.* A counterfactual test could in principle notice a dependence the
record does not declare; a declared-input test cannot. **H5** is exactly the
hypothesis that makes that safe, which is why it is stated rather than assumed,
and `cases.partial_effect_pair` is a record where it fails.

**Unique issuance.** Dissolved by occurrence identity (§2).

**The account layer.** Answerability is not in the headline object and this pass
did not put it back. `CROSS_PROCESS_INTERFACE.md` §5 carries what it is for.

## 8. The realization

`src/ri_frame.py` is the map.

```text
occurrence   a standing id — a seed id, or `@s{tau}.{i}`, which already carries
             the issuing index
sort         PAuth and PProto are authority; PValue, PForce and PCmt are norm
edit         a NormEvent
grounds      schemaRef, plus the authority-sorted Supersede targets where it issues
dispose      targetsN(effect)          issue   the fresh ids with their payloads
input        the settlements the event's reason leaves draw on
exercise     the author and the derivation's leaves
request      (schemaRef, witness)
alpha        the episodes currently doubted
```

| hypothesis | in the realization |
|---|---|
| **H1** | `[THM]`. `Std_t` moves only through `applyEffect` on a well-formed `Norm` step. |
| **H2** | `[THM]`. `tag(tau, i)` with `F1` injective and `F2` disjoint from the seed. |
| **H3** | `[THM]`. `G4` and `G6` resolve `schemaRef` and every target in the strict pre-state. |
| **H4** | `[THM]`, **and thin.** `PAuth` carries a `SchemaCode` and no domain, so `permit` is the identity except where a `PProto` ground supplies `covers`. A record whose authority is a bare `PAuth` satisfies H4 vacuously. |
| **H5** | `[THM]` where the record's schemas read only what its events declare, and **false otherwise** — `cases.partial_effect_pair`. |
| **H6** | `[THM]` for the implication; the adequacy half is `[AXM]`. |

**Realization theorem.** A Reflective Integrity record whose schemas read only
declared inputs proposes an edit sequence satisfying H1-H6, so G1-G6 hold of it.
`[THM]`, run as a check on ten records in `test_replay.py`.

**H4 is where the realization is thinnest and the round says so rather than
hiding it.** Reflective Integrity has no jurisdiction field on an authority. That
is a gap in the architecture the abstraction exposes, not a gap in the
abstraction.

## 9. What the compression cost, in one line each

Answerability left the headline in the previous pass and did not come back.
Delegation of *custody* — Reflective Integrity's `Transfer` — is now a no-op on
the legitimate state, because the state has no holder field; delegation of
*authority* is an ordinary edit and `office.audit_discovery`'s appointment is
one.

The certificate is the grounding tree of G1 and no longer carries stability
judgments, because there are none to carry. What a recipient must be able to
evaluate is `Valid`, and `CROSS_PROCESS_INTERFACE.md` §3 is what that costs.
