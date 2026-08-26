# Legitimate evolution

Status: **specification and reference models; unregistered.** All names are
provisional under `AGENTS.md` §6. The statements are paper derivations, each
exercised by finite frames in `src/` and `tests/`; nothing is Lean-checked and no
claim is registered. `test-supported` is the ceiling.

Tags: `[DEF]` true by the type · `[THM]` derived · `[ASM]` a hypothesis on a
parameter · `[AXM]` a substantive input the mathematics does not supply.

---

## 1. Two layers, and which one is the theorem

```text
                succession frame  +  L0-L4  +  coverage        §§2-6
                          |
                          |   T1-T5, recognition transport
                          v
   legitimate evolution, a legitimately live frontier, two projections
  ------------------------- realization boundary -------------------------
   Reflective Integrity, standing replay, reason provenance,
   answerability succession, challenged replay                    §8
                          |
                          |   realization theorem
                          v
                 satisfies L0-L8 (L3' under one named condition)
```

Nothing above the boundary names a normative event, a reason occurrence, an
answerability root or a replay. `src/warrant.py` builds frames out of a register
of offices and appointments, imports `frame.py` and nothing else of this
repository's, and settles three questions our own architecture cannot see.

## 2. The succession frame

```text
A                 authorities     opaque; whatever may govern something
T                 exercises       acts that act on, inherit from, and put in force
affected(t)       the positions the exercise acts on
parents(t)        the authorities its issue inherits entitlement from
tgt(t)            what it leaves in force
lic(t)            the authority the actor held
rank              a well-founded precedence
when(t)           the lifecycle index at which it happened
G subset A        the base a recognizing process accepts
live[s]           the lifecycle view at index s, externally supplied
Q                 challenges      "suppose this influence had not occurred"
Chal : Q -> Pfin(T)               the exercises a challenge is about
|= subset Q x (A + T)             stability
issued(t)  := tgt(t) \ affected(t)
grounds(t) := parents(t) union {lic(t)}
```

Three separations, each forced by a countermodel rather than chosen.

**`affected` is not `parents`.** Acting on an authority is not inheriting from
it. A regulator revoking a fraudulent warrant and granting a proper one acts on
the fraudulent one and inherits from its own charter, and a rule that read the
objects acted on would make the replacement illegitimate. `COUNTERMODELS.md` §2.

**Stability is not legitimacy.** `q |= x` says `x` survives the challenge. It does
not say `x` is entitled to anything, and the licence of an exercise is now
required to be *derivable*, not merely stable. `COUNTERMODELS.md` §1 is the
frame on which the difference made the previous pass's headline theorem false.

**Form is not coverage.** The axioms constrain the shape of a legitimacy
calculus. Whether its challenge set reaches the influences anyone cares about is
a separate hypothesis with its own type. §6.

Nothing in the frame is content. `A` is a set of tokens; what an authority *says*
has no field, so no clause below can read it.

## 3. The spine

**L0 — base stability.** `forall q in Q, g in G. q |= g`.
*What the recognizing process already accepts is not something the challenged
influence produced.* The round's one unavoidable substantive input on the
legitimacy side; legitimacy is definable only relative to a base, and this is
where that shows. `[AXM]`

**L1 — precedence.** For every `t`: everything in `affected(t) ∪ grounds(t)`
precedes `t`, and `t` precedes everything in `issued(t)`.
*You cannot supersede what does not yet exist, inherit from what has not been
granted, act under a warrant you have not been given, or be licensed by what your
own act creates.* `[ASM]`

**L2 — no ex nihilo authority.** Every `y in A \ G` lies in `issued(t)` for some
`t`. *Authority does not appear from nowhere.* `[ASM]`

**L2' — unique issuance.** No `y` is issued twice and no base authority is
issued. **Optional**, and out of the checked spine: every theorem except
canonicity is proved without it. `[ASM]`

**L3 — issuance stability.** `q |= t  =>  forall y in tgt(t). q |= y`.
*If the act would still have been performed, what it put in force would still be
in force.* `[ASM]`

**L3' — origin necessity.** For `y notin G`: `q |= y  =>  some issuer of y is
stable under q`.
*The only way this authority could be there is that it was granted; if every
granting act is void under the challenge, so is the authority.* Stated over
issuers rather than over a unique issuer, so that it does not smuggle L2'.
`[ASM]`

**L4 — challenge bite.** `t in Chal(q)  =>  not (q |= t)`.
*The counterfactual is about something.* `[ASM]`

L3 and L3' are converses and are not the same hypothesis. Which one a
realization has to work for depends on how it individuates an exercise, and §8
is the prosecution of that.

## 4. Certified succession

```text
G |-_q y   :=   y in G,  or
                exists t.  grounds(t) subset { z : G |-_q z }
                       and y in tgt(t)
                       and q |= t

G |- y     :=   forall q in Q.  G |-_q y
```

**The licence is a ground.** Requiring only `q |= lic(t)` lets an exercise
inherit recognition from an authority that survives the challenge without being
entitled to anything. `frame.derivable_stable_licence` is the rejected rule, kept
so the two run side by side on the frame that separates them.

**All of `parents(t)`, and `affected(t)` is not consulted.** An exercise inherits
from what it inherits from; acting on an illegitimate standing in order to end it
is not inheriting from it.

**Challenges are quantified over, never composed.** Each judgment is taken at one
challenge and no verdict is assembled across two, which matters because the
Reflective Integrity challenge operator is neither monotone nor composable.

**T1 — lineage existence.** Under L1 and L2 every authority has a finite
`rank`-well-founded provenance whose minimal elements lie in `G`. No legitimacy
clause takes part and **L2' is not used**: the closure runs over every issuer, so
a branching origin costs the theorem nothing. `[THM]`

T1 is why the theory is not a restatement of a recursive definition. *Having* a
lineage is earned from L1 and L2; *having a certified one* is the extra content;
and they come apart on a record where a manufactured protocol is in force,
reaches the seed, and is not derivable.

**T1' — canonicity, under L2'.** The provenance is determined by the target, so a
process cannot present a flattering route. This is the whole of what unique
issuance buys. `[THM]`

**T2a — stability of the derivable.** L0 + L3 give `G |-_q y => q |= y`.
Induction: the base is L0 and each step is L3. With the repaired rule this also
yields `q |= lic(t)` for every certified `t`, so the old side condition on
licences is now a consequence. `[THM]`

**T2 — no self-ratifying authority.** L0 + L3 + L3' + L4 give: for every
derivable `y` there is a certified derivation none of whose exercises is
challenged and each of whose authorities has an unchallenged issuer.

*Proof.* Take the derivation the fixed point produces. Every step is stable, so
L4 puts it outside `Chal(q)`. Every `z` in its ancestry is derivable — which is
what the repaired rule guarantees and the old one did not — so T2a gives `q |= z`,
L3' gives a stable issuer, and L4 puts that issuer outside `Chal(q)`. ∎ `[THM]`

The obligation discharged at each step is stability of one exercise and
derivability of what it inherits from; the conclusion is about every ancestor of
the result at every depth. **Under L2' the existential over issuers collapses**
and the statement becomes one about the target's determined provenance.

**Why the theorem is about a derivation and not about the provenance.** With two
issuers for one authority, the route-blind provenance contains both, and a
challenged issuer may sit in it while the authority is perfectly derivable by the
clean route. `warrant.two_issuers_register` is that frame. A theorem quantifying
over the union would be false there and the certificate would be unshowable.

**T3 — content independence.** For any `content : A -> C` and any injection on
`C`, relabelling leaves `G |- y` unchanged. `[DEF]` at the abstract level, and a
falsifiable condition on a realization: a representation whose succession clauses
inspected what an authority says would map onto no frame at all.

## 5. The legitimately live frontier

The frame carries an externally supplied lifecycle view. A legitimacy calculus
says which authorities are entitled; which are in force is a different question
with a different answer, and conflating them leaves a consumer unable to tell
what to enforce.

```text
F^leg_s  :=  live[s]  intersect  { y : G |- y }
```

**L5 — lifecycle entry.** An authority enters `live` at the base or by being
issued by an exercise happening then. `[ASM]`
**L6 — lifecycle exit.** An authority leaves `live` only by being acted on by an
exercise happening then. `[ASM]`

**T4 — persistent until legitimately changed.** Under L6, `x in F^leg_s` and no
exercise in `(s, u]` with `x in affected(t)` give `x in F^leg_u`. Derivability
does not move with the lifecycle index, so only the live view can change, and by
L6 it changes only through an exercise acting on `x`. `[THM]`

Not *once legitimate, always legitimate*. There are exactly two exits.

**T4' — the second exit: legitimacy is antitone in challenges.** Adding
challenges can only shrink what is derivable, so an authority can leave the
frontier with nothing acting on it — by the arrival of a challenge reaching its
lineage. `[THM]`

That is a feature rather than a leak. A recognizing process that learns of an
influence it did not know about revises downwards, which is what one would want,
and it is why `F^leg` is not a monotone object.

**Two projections, one frontier.** `AuthorityView_s` and `NormView_s` are
`F^leg_s` filtered by a classifier the consumer supplies. The frame does not know
what a norm is. `cases.force_bearing` is the record where the norm projection is
a real set: one injunction legitimately superseded, one manufactured beside it,
and the frontier holds the successor while the manufactured one is live and
outside it.

## 6. Coverage, and what the theorem is relative to

```text
ThreatModel = ( Xi , depends : Xi -> Pfin(T) )

Coverage    :  forall xi in Xi.  exists q in Q.  depends(xi) subset Chal(q)
```

**C — challenge coverage.** *The calculus asks about the influences anyone is
worried about.* `[AXM]`

Not derivable from anything. `depends` is a fact about the world and about the
process's own provenance discipline, and no counterfactual over a record computes
it. What the frame can do is make the hypothesis a field with a type, so that a
certificate says what it is a certificate against.

```text
certified_against(f, Xi)  =  {} when Coverage fails, whatever the spine says
```

A frame with no challenges satisfies L0-L4 vacuously and derives everything;
`warrant.undercovered_register` is exactly that frame, and the threat model is
what refuses it. A certificate offered against an uncovered threat is not a
weaker certificate — `certify` returns nothing.

**The honest ceiling on self-certification.** A record's own declared episodes
generate a threat model its challenge set covers by construction
(`ri_frame.threat_from_episodes`). A recognizing process worried about an
influence the record does not record must supply its own threat model, against
which the record may simply fail. That is the right shape and it is not a
solution to provenance completeness.

## 7. Answerability, and why it is not in the spine

```text
Acc, holder, subject, ends : T -> Pfin(Acc), opens, answered
L7  carriage      subject(ends t) = affected(t),  subject(opens t) = tgt(t)
L8  trichotomy    open | outstanding | answered; none removed
```

**T5 — visible discontinuity.** Under L7 and L8 an account fails continuity
exactly when one beneath it is outstanding. `[THM]`

**No theorem of §4 or §5 reads the account layer.** A transfer under a licensed
schema whose ended episode is never answered has a clean spine, a derivable
authority, and an account outstanding forever. Answerability is therefore not
constitutive of the authority, and putting it in `|-` would refuse a case in
which nothing about the authority is wrong.

What it does earn: **delegation** is an exercise with `affected(t) = tgt(t)`,
which issues nothing and is a self-loop on the authority graph; **disposal** is
an exercise with `tgt(t) = {}`, which the authority graph does not record at all;
and **T5**, the only clause of the whole interface that can fail with the
authority side clean.

## 8. The realization

`src/ri_frame.py` is the map, and §§2-7's objects go to Reflective Integrity's as
the module's table records. Two things in it are decisions rather than
transcriptions.

**`parents` is not `targetsN(effect)`.** A `Supersede` that issues inherits from
what it supersedes; a `Supersede` with no payloads issues nothing and inherits
nothing; a `Create` inherits from its licence alone; a `Transfer` re-issues what
it acts on. So a record expresses a cleanup as a revocation plus a separate
creation, and `cases.record_cleanup` is that record: the replacement is derivable
and the tainted standing is not.

**`Chal` is read forward off the reason ledger and stability backward off the
replay.** Defining `Chal(q)` as the non-survivors would make L4 true by
stipulation and establish nothing about the challenge operator.

### 8.1 What an exercise is, and where the hypothesis lives

```text
identity = "event"    q |= t  iff the event id is admitted in the excised replay
identity = "effect"   q |= t  iff it is admitted and produces the same effect
```

The first pass used event identity and found **L3** then needs the record's
schemas to be pre-state-blind: an event can survive and mint the same identifier
carrying a different payload, which is the Carroll round's `C28`.

Prosecuting the map rather than the axiom shows the hypothesis **moves rather
than vanishing**. Under effect identity a differently-acting event is a different
exercise, so L3 holds outright and `C28` is repaired — but an event whose effect
changes in *one* component can leave another component's authority untouched, and
then the authority survives while no exercise of the frame does, which refutes
**L3'**. `cases.partial_effect` is that record, and it fails L3 under one
identity and L3' under the other.

| | L3 | L3' |
|---|---|---|
| event identity | needs pre-state-blindness | free |
| effect identity | free | needs pre-state-blindness |

**So pre-state-blindness is not an artefact of a coarse realization map.** It is
the record-level condition that makes the challenge operator's action on effects
determinate, and it is required under either identity. The identity is therefore
chosen on semantics rather than to shed a hypothesis, and the round takes effect
identity as the default because an act that does something else is not the same
exercise.

### 8.2 The realization table

| axiom | in the realization |
|---|---|
| **L0** | `[THM]`. Excision voids an episode's settlements; the seed is not a settlement. |
| **L1** | `[THM]`. `G4` and `G6` resolve `schemaRef` and every target in the strict pre-state; Fresh Allocation puts every issued id at `tau(a)`. |
| **L2** | `[THM]`. Every standing is a seed id or a `tag(tau, i)` from `freshN`. |
| **L2'** | `[THM]`. `F1` and `F2`; and it is not needed by anything above canonicity. |
| **L3** | `[THM]` under effect identity, unconditionally. |
| **L3'** | `[THM]` under effect identity **where the record's schemas are pre-state-blind**, and false otherwise. |
| **L4** | `[THM]` for this operator: an event whose derivation cites a reason drawing on a removed settlement fails `G2`, and the cascade replaces it. |
| **L5 / L6** | `[THM]`. `Std_t` moves only through `applyEffect` on a well-formed `Norm` step, and §12.3's TargetCoverage is exactly the exit clause. |
| **L7 / L8** | `[THM]`. §15.2 disposes the current episodes of `targetsN` and §17 mints one per `episodes(a)`; trichotomy is §19 and no-removal is `AC(i)`. |

**Realization theorem.** A Reflective Integrity record whose schemas are
pre-state-blind, with the Carroll challenge operator and effect-identified
exercises, is a succession frame satisfying L0-L4, a lifecycle satisfying L5-L6
and an account layer satisfying L7-L8; hence T1-T5 hold of it. `[THM]`, run as a
check on every fixture in `test_frame.py`.

## 9. What the realization costs that the interface does not

The interface treats `|=` as an oracle. What implementing it costs is a fact
about the realization:

- in `warrant.py` stability is a monotone reachability query over a dependency
  graph, and both L3 and L3' are free;
- in `ri_frame.py` it is a replay of the record under a voided episode, the
  operator is neither monotone nor composable, and the pre-state condition of
  §8.1 is live.

The consequence for a certificate is that the derivation compresses and the
stability half does not. `CROSS_PROCESS_INTERFACE.md` §3 is what follows for a
recognizing process.
