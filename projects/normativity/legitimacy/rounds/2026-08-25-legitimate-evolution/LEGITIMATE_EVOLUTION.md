# Legitimate evolution

Status: **specification and reference model; unregistered.** All names are
provisional under `AGENTS.md` §6. The statements are paper derivations, each
exercised by finite records in `src/` and `tests/`; nothing is Lean-checked and
no claim is registered. `test-supported` is the ceiling.

Tags: `[DEF]` true by the type · `[THM]` derived · `[ASM]` a hypothesis on a
parameter · `[AXM]` a substantive input the mathematics does not supply.

---

## 1. Two layers, and which one is the theorem

```text
                 succession frame  +  L0-L4        §§2-4
                          |
                          |   T1-T4, RecognitionTransport
                          v
        legitimate evolution and cross-process recognition
  ------------------------- realization boundary -------------------------
   Reflective Integrity, standing replay, reason provenance,
   answerability succession, challenged replay                    §7
                          |
                          |   realization theorem
                          v
                 satisfies L0-L4 (L3 conditionally)
```

Nothing above the boundary names a normative event, a reason occurrence, an
answerability root or a replay. `src/warrant.py` builds a frame out of a
register of offices and appointments, imports `frame.py` and nothing else of
this repository's, satisfies the whole spine, and refuses a laundered warrant —
which is what makes the separation a checked fact rather than a stylistic
preference.

---

## 2. The succession frame

```text
A                 authorities        opaque; whatever may govern something
T                 exercises          acts that consume and issue authorities
src, tgt : T -> Pfin(A)              what an exercise consumes; what it puts in force
lic      : T -> A                    the authority the actor held
rank     : A + T -> W                any well-order
G        subset A                    the base a recognizing process already accepts
Cur      subset A                    the authorities in force now
Q                 challenges         "suppose this influence had not occurred"
Chal     : Q -> Pfin(T)              the exercises a challenge is about
|=       subset Q x (A + T)          stability: u still stands when q is granted
issued(t) := tgt(t) \ src(t)
```

`issued` rather than `tgt` is what makes delegation a case rather than a
degeneracy. An exercise that hands the same authority to a new holder has
`tgt(t) = src(t)`, issues nothing, and opens no second origin. `[DEF]`

Nothing in the frame is content. `A` is a set of tokens; what an authority
*says* has no field, so no clause below can read it. §5 is the consequence.

## 3. The spine

Each axiom below has a reading that constrains an external object, a system
satisfying it without this repository's architecture, and a failure mode.
`COUNTERMODELS.md` prosecutes each.

**L0 — base stability.** `forall q in Q, g in G. q |= g`.
*What the recognizing process already accepts is not something the challenged
influence produced.* This is the round's one unavoidable substantive input on
the legitimacy side. Legitimacy is definable only relative to a base, and L0 is
where that shows. `[AXM]`

**L1 — precedence.** `x in src(t) => rank x < rank t`; `rank (lic t) < rank t`;
`y in issued(t) => rank t < rank y`.
*You cannot supersede what does not yet exist, act under a warrant you have not
been given, or be licensed by what your own act creates.* `[ASM]`

**L2 — no ex nihilo authority.** Every `y in A \ G` is in `issued(t)` for some
`t`. *Authority does not appear from nowhere.* `[ASM]`

**L2' — unique issuance.** No `y` is issued by two exercises, and no base
authority is issued. *An authority has one origin.* Used only for canonicity;
§4 says exactly what it buys. `[ASM]`

**L3 — issuance stability.** `q |= t  =>  forall y in tgt(t). q |= y`.
*If the act would still have been performed without the challenged influence,
what it put in force would still be in force.* `[ASM]`

**L3' — origin necessity.** For `y notin G`: `q |= y  =>  q |= mint(y)`.
*The only way this authority could be there is that it was granted; if the
granting act is void under the challenge, so is the authority.* `[ASM]`

**L4 — challenge bite.** `t in Chal(q)  =>  not (q |= t)`.
*The counterfactual is about something.* An operator that named an influence and
left the acts it produced standing would satisfy L0-L3' and establish nothing.
`[ASM]`

L3 and L3' are converses and they are not the same hypothesis. Splitting them is
this round's sharpest structural finding: in the Reflective Integrity
realization **L3' holds from the identifier scheme alone and L3 needs the
schemas to be pre-state-blind** (§7), which is the Carroll round's `C28` read as
a fact about the interface rather than about the criterion.

## 4. Certified succession, and what it earns

```text
Certified_q(t)  :=  q |= lic(t)  and  q |= t

G |-_q y   :=   y in G,  or
                exists t.  src(t) subset { z : G |-_q z }
                       and y in tgt(t)  and  Certified_q(t)

G |- y     :=   forall q in Q.  G |-_q y
```

**All** of `src(t)`, not one of it. An exercise superseding two authorities
inherits from both, so a lineage through the clean one of a pair does not carry
the pair. `COUNTERMODELS.md` §5 is the laundering that refuses.

Quantifying over challenges rather than composing them is forced. The Carroll
round refuted monotonicity and composition of the challenge operator from two
independent sources, so a relation defined by excising a union of challenges
would rest on an algebra that does not hold. Each judgment here is taken at one
challenge and no verdict is assembled across two.

**T1 — `|-_q` is a partial order with finite derivations.** By L1 the exercise
relation is `rank`-forward, so the least fixed point above is reached in
finitely many steps and contains no cycle. `[THM]`

**T2 — lineage existence.** Under L1 and L2, every `y in A` has a finite
`rank`-well-founded provenance — the closure of `y` under `src(mint(·))` and
`lic(mint(·))` — whose minimal elements lie in `G`. **No legitimacy clause takes
part.** `[THM]`

T2 is why the theory is not a restatement of a recursive definition. *Having* a
lineage is earned from L1 and L2 alone; *having a certified one* is the extra
content, and the two come apart on a record: in `C10` the manufactured protocol
is in force, has a provenance reaching the seed, and is not derivable.

**T2' — canonicity.** Under L2' the provenance of `y` is determined by `y`. A
process cannot present a flattering lineage, because there is only one. Without
L2' lineage still exists and stops being unique, which is the whole of what L2'
buys. `[THM]`

**T3a — stability of the derivable.** L0 + L3 give `G |-_q y => q |= y`.
Induction on the derivation: the base is L0, each step is L3. `[THM]`

**T3 — no self-ratifying authority.** L0 + L3 + L3' + L4 give: if `G |-_q y`
then no `z` in the provenance of `y`, at any depth, was issued by an exercise in
`Chal(q)`.
*Proof.* Each such `z` is itself derivable, so `q |= z` by T3a; L3' gives
`q |= mint(z)`; L4 gives `mint(z) notin Chal(q)`. ∎ `[THM]`

T3 is the local-to-global result. The obligation discharged at each step is
stability of one licence and one exercise; the conclusion is about every
ancestor of the result at every depth, and it is the sense in which an authority
cannot obtain the entitlement by which it is licensed from structure that exists
only because of the challenged influence.

## 5. Content

The frame has no content field, so no clause of `|-` can read what an authority
says. Stated as a theorem about any content assignment:

**T4 — content independence.** For any `content : A -> C` and any injection
`sigma` on `C`, relabelling the content leaves `G |- y` unchanged. `[DEF]` at the
abstract level.

At the abstract level this is true by the type and is therefore cheap. Its
force is that it becomes a **falsifiable condition on a realization**: a
representation whose succession clauses inspected what a standing says would map
onto no frame at all. `test_frame.py` runs the corresponding check on a record,
relabelling every value specification and comparing the derivable sets.

Three witnesses that authority survives genuine change, each an existing
fixture read through the frame:

| | | |
|---|---|---|
| revision | `C14` | the successor is derivable and says something else |
| delegation | `delegated_custody` | the authority is unchanged and the holder is not |
| later independent adoption | `C33` | the value an unlicensed influence produced is legitimately installed afterwards, and the influence stays unlicensed |
| no temporal dictatorship | `C11` | two trajectories to one cognitive endpoint; one derivable, one not |

## 6. Answerability, and why it is not in the spine

The account layer is separate data:

```text
Acc                        accounts
holder   : Acc -> Party
subject  : Acc -> A
ends     : T -> Pfin(Acc)  the accounts an exercise closed out
opens    : T -> Pfin(Acc)  the accounts it opened
answered : Acc -> Bool
```

**L5 — account carriage.** `subject(ends t) = src(t)` and
`subject(opens t) = tgt(t)`. `[ASM]`
**L6 — trichotomy.** Every account is exactly one of *open* (ended by nothing),
*outstanding* (ended, unanswered), *answered*; and no account is removed. `[ASM]`

**T6 — visible discontinuity.** Under L5 and L6, an account fails continuity
exactly when some account beneath it is outstanding, where continuity is: open,
or answered with every successor continuous. Well-founded induction along
`opens`, which is `rank`-forward by L1 and L5. `[THM]`

Three facts settle answerability's role, and the first is negative.

**No theorem of §4 reads the account layer.** `delegated_custody(answered=False)`
is a record whose spine is clean, whose authority is derivable against every
challenge, and whose base account is outstanding forever. Recognition of the
*authority* transports; the process's account does not close. So answerability is
**not constitutive of the authority** and does not belong in `|-`.

**Delegation is expressible only here.** An exercise with `src(t) = tgt(t)`
issues nothing: on the authority graph it is a self-loop carrying no lineage,
and on the account graph it is an edge between two holders. Without the layer
the interface cannot tell delegation from a no-op. `[THM]`, `T5`

**Disposal is expressible only here.** An exercise with `tgt(t) = {}` and
`src(t) != {}` ends an authority and issues no successor; the authority graph
records no edge at all, so on the spine alone a revocation and a thing that
never happened are the same. The account it ends is the only trace. `[THM]`,
`T5'`

So the account layer earns two constructors the spine cannot express, and a
third fact a recognizing process wants and the spine cannot supply. What it does
**not** earn is a clause of legitimate succession.

**T6 is the only clause of the whole interface that can fail with no
authority-side defect.** That is its use, and §5 of `CROSS_PROCESS_INTERFACE.md`
is where it lands.

## 7. The realization

`src/ri_frame.py` is the map.

```text
authority   StandingId                     exercise    NormEvent
src         Supersede targets, or a Transfer's subject
tgt         the fresh ids, or a Transfer's subject
lic         schemaRef                      rank        tau
G           dom(Std_0)                     Cur         the Active standings
Q           an influence episode's ancestry class
Chal(q)     the events whose derivation reasons from a challenged settlement
q |= x      the standing arises in the excised replay carrying its own payload
q |= a      the event is admitted in the excised replay
Acc         AnsRoot        ends/opens   Disposes/MINT       answered   Closed
```

`Chal` is read forward off the reason ledger and stability backward off the
replay. That is not an implementation convenience: defining `Chal(q)` as the
non-survivors would make **L4** true by stipulation and establish nothing about
the challenge operator.

| axiom | in the realization |
|---|---|
| **L0** | `[THM]`. Excision voids an episode's settlements; the seed is not a settlement and no replay can remove it. |
| **L1** | `[THM]`. `G4` and `G6` resolve `schemaRef` and every target in the strict pre-state; Fresh Allocation puts every issued id at `tau(a)`. |
| **L2** | `[THM]`. Every standing is a seed id or a `tag(tau, i)` produced by `freshN`. |
| **L2'** | `[THM]`. `F1` makes `tag` injective and `F2` disjoint from `dom(Std_0)`, so two events cannot mint one id. |
| **L3** | `[THM]` **under pre-state-blindness**, and false without it. A surviving event whose schema reads the strict pre-state mints the same id with a different payload — the Carroll round's `C28`, which `test_frame.py` runs in both arms. |
| **L3'** | `[THM]`. A non-seed id is `@s{tau}.{i}`, `tau` is preserved by excision, and only the event at that `tau` can mint it; if the standing is present in the excised replay that event was admitted. |
| **L4** | `[THM]` for this operator. An event whose derivation cites a reason drawing on a removed settlement fails `G2`, and the cascade replaces it. |
| **L5** | `[THM]`. §15.2 disposes exactly the current episodes of `targetsN`, and §17 mints one per `episodes(a)`. |
| **L6** | `[THM]`. Trichotomy is RI §19; no-removal is `AC(i)`. |

**Realization theorem.** A Reflective Integrity record whose practical schemas
are pre-state-blind, together with the Carroll challenge operator, is a
succession frame satisfying L0-L4 and an account layer satisfying L5-L6; hence
T1-T4 and T6 hold of it. `[THM]`, run as a check on every fixture in
`test_frame.py`.

RI's own Due-Witness (§24) is T6 in the realization, and its Fresh Allocation
(§13) is L2 and L2'. Neither is reproved here; the content of the realization is
that they are instances.

## 8. What the realization costs that the interface does not

The interface treats `|=` as an oracle. A realization has to implement it, and
what that costs is a fact about the realization rather than about legitimacy:

- in `warrant.py` stability is a monotone reachability query over a dependency
  graph, and **L3 is free**;
- in `ri_frame.py` stability is a replay of the record under a voided episode,
  and **L3 is a hypothesis** that a legal record can violate.

The consequence for a certificate is §3 of `CROSS_PROCESS_INTERFACE.md`: the
derivation is finite and cheap in every realization, and the stability half
compresses in some and not in ours.
