# Grounded Replay

Status: **specification and reference models; unregistered.** All names are
provisional under `AGENTS.md` §6. The statements are paper derivations exercised
by finite processes in `src/` and `tests/`; nothing is Lean-checked and no claim
is registered. `test-supported` is the ceiling.

---

This document is the **entitlement** half. Its counterpart on the
non-entitlement half, and the one-page statement of the two together, is
`ANSWERABILITY.md`. Nothing in this document was changed by that round: the
kernel was frozen and is unchanged.

## MINIMAL MATHEMATICAL STATEMENT

**Types.**

```text
Occ    = (pos : Nat + {G},  slot : Nat)          an occurrence
Edit   = (grounds : Pfin Occ,  dispose : Pfin Occ,  issues : List C,
          declared : D)                          C, D opaque
State  = Pfin Occ
```

**Data.** A base `G : State`, a trace `e_0 ... e_{T-1} : List Edit`, a predicate
`Auth : Occ -> Prop`, a relation `Valid : State -> Edit -> Prop`.

**Definitions.**

```text
issue_t(e)   = { (t, i) : i < |issues(e)| }
apply_t(L,e) = (L \ dispose(e)) union issue_t(e)

L_0          = G
L_{t+1}      = apply_t(L_t, e_t)   if Valid(L_t, e_t)
               L_t                 otherwise

Adm_t        = G union { issue_s(e_s) : s < t accepted }
Acc          = { t : Valid(L_t, e_t) }
```

**Premises.** For every accepted `t`:

```text
S1   grounds(e_t) subset { o in L_t : Auth(o) }
S2   apply_t(L_t, e_t) != L_t   ->   grounds(e_t) != {}
```

**Theorem (Grounded Replay).** Under S1 and S2, for every `t <= T` and every
`o in Adm_t` there is a finite tree `pi_o` with root `o`, leaves in `G`, each
internal node `x` issued by an accepted edit `e_s` with children `grounds(e_s)`,
and every child's `pos` strictly less than `s`.

*Proof.* Induction on `t`. `Adm_0 = G`; a base occurrence is its own tree. At an
accepted `t`, S1 puts `grounds(e_t)` in `L_t ⊆ Adm_t`; every element of `Adm_t`
lies in `G` or has `pos < t`; the induction hypothesis gives each a tree; S2
makes `grounds(e_t)` non-empty whenever `e_t` issues, so no issued occurrence is
a leaf outside `G`. Hang those trees under `t`. ∎

**Corollary 1 (no self-ratification).** No accepted `e_t` has
`grounds(e_t) ∩ issue_t(e_t) != {}`. By S1 the grounds lie in `L_t`, and every
member of `issue_t(e_t)` has `pos = t`, which nothing in `L_t` does.

**Corollary 2 (no laundering).** If `t` is rejected then
`issue_t(e_t) ∩ Adm_T = {}`. A rejected edit is a no-op, and every occurrence any
other edit issues carries that other edit's position.

**Corollary 3 (persistence).** If `o in L_s` and no accepted `u in [s,t)` has
`o in dispose(e_u)`, then `o in L_t`.

**One counterexample per premise.**

| premise | drop it | what fails |
|---|---|---|
| **S1** | an edit grounded in an occurrence nobody issued, accepted | the theorem: what it issues has **no tree** |
| **S2** | an edit with empty grounds, accepted, issuing | the theorem: the issued occurrence's only tree is itself, **a leaf outside `G`** |

They fail on different frames, so neither subsumes the other.

**Definitional versus inductive.** Freshness is definitional — the trace is a
list, so positions are unique and `issue_t` is disjoint from everything earlier.
Determinism of the fold is definitional — the effect is inside the edit.
Corollaries 1 and 3 are two lines each. **The theorem is an induction and
Corollary 2 depends on the identity choice**; those are the two places anything
is earned.

**Structural, semantic, realization.**

```text
structural     Occ, Edit, State, replay, S1, S2, the theorem, the corollaries
semantic       Valid, and what defines it: Permit, ProvView, ProvComplete
realization    the extraction of (base, trace, Auth, Valid) from a raw process
computational  a checker Check against the semantic Valid
```

Nothing in the structural column mentions the others. `tests/test_replay.py`
checks that by reading the kernel's identifiers.

---

## 1. What the kernel is not about

`Valid` is a **parameter**. No theorem above assumes it is any good, and the
substantive content of legitimacy is not here. What is here is that a
reconstructed state has a grounded history, that rejected occurrences never
enter it, and that it changes only when an accepted edit changes it.

## 2. The semantic layer

`src/office.py` **defines** validity rather than constraining it:

```text
Valid_alpha(L, e)  :=  grounds(e) subset Auth(L)
                   and (changes(L,e) -> grounds(e) != {})
                   and ProvComplete_alpha(e)
                   and Permit(L, e, ProvView_alpha(e))
```

The previous formulation kept `Valid` primitive and assumed three implications
about it, leaving it free to reject an edit that was grounded, permitted and
provenance-adequate for no stated reason. Nothing needed that freedom, and the
first two clauses are exactly S1 and S2.

**Descriptive and normative are separated.** `ProvView` answers *did Bob argue,
was this forged, was Alice coerced*. `Permit` answers *is persuasion allowed, does
forgery count as an exercise, may this office act on this subject*. The previous
`ProvOK` could only refuse an influence, which is why persuasion had to be an
exception; here Bob's argument appears in the view and the edit is permitted.

`Permit` may read content, and does: a live policy banning a scope refuses an
edit in it. That is why content invariance is **withdrawn** rather than restated.

## 3. Lineage is not currentness

```text
Grounded(o)   o has a finite authorization lineage
Admitted(o)   an accepted edit issued it, or it is in G
Live_t(o)     o in L_t
```

`Live_t ⊆ Admitted`, and **on a fixed trace `Grounded = Admitted`** — a lineage
is built from the accepted edits of that trace, so having one and having been
issued by one coincide. What is independent is admitted against live, and
`office.lineage_versus_current` is the process where an authority is validly
issued, validly used, and validly revoked: it keeps its tree and stops being in
force.

**A grounding tree certifies that an occurrence was legitimately issued. It
cannot certify that it is still in force**, because it names no disposal.
`CROSS_PROCESS_INTERFACE.md` §3 is what a current-state claim costs instead.

## 4. Checkers

`Valid` is semantic; a `Check` is computable. The exact relation:

```text
agrees on the trace:   for every t,  Check(L_t, e_t) <-> Valid(L_t, e_t)
```

**Simulation.** Agreement along the trace gives `Lhat_t = L_t` for every `t`, by
induction on equal states with equal verdicts.

It is weaker than global extensional equality — it says nothing about states the
trace never reaches, and a checker that is wrong everywhere else still simulates.
It is strictly stronger than one-sided soundness, and that matters:
**`Check(Lhat,e) -> Valid(Lhat,e)` is worth nothing.** A checker that misses a
valid revocation keeps an authority the semantics removed and then evaluates every
later verdict against a state that never legitimately existed.
`COUNTERMODELS.md` §3.

## 5. The realization

`src/ri_frame.py` **extracts** `(base, trace, Auth, Valid)` from a Reflective
Integrity record: seed standings are base occurrences, events are trace
positions, `schemaRef` and the authority-sorted supersession targets are grounds,
`targetsN` is `dispose`, the fresh payloads are `issues`, and the settlements the
event's reasons draw on are the declared provenance.

**Hidden-state noninterference is a composition**, and neither half is new:

```text
extraction factorization    same declared data -> same trace and same Valid
fold determinism            same base, trace and Valid -> same replay
```

The second is definitional. The first is the substantive claim and it can fail
two ways: a record whose effect reads an uncited settlement produces a different
**trace** (`cases.partial_effect_pair`), and a process whose validity rules read
hidden state produces a different **Valid** (`office.hidden_reading_pair`). So the
old H5 is not a legitimacy premise; it is a conformance condition at the
extraction boundary.

**Permission is thin here and the round says so.** `PAuth` carries a `SchemaCode`
and no domain, so jurisdiction bites only where a `PProto` ground supplies
`covers`. `PRIORITIES.md` item 67; this pass does not repair it.

## 6. What coverage is, exactly, and why it is left open

`ProvComplete_alpha(e)` says the descriptive view exposes every `Xi`-relevant
dependency of the authorization judgment. The round tried to state it
non-circularly and did not succeed. What it is **not**:

- not "assume all relevant influences are visible" — that is the same sentence;
- not "refuse every influence" — that refuses persuasion;
- not derivable from the record, which is what a record's own episodes covering
  by construction amounts to.

It is therefore an **explicit epistemic assumption on the extraction**, carried as
a boolean the realization must justify, and `office.incomplete_provenance` is the
process where it is false and the edit is refused. It is not a premise of Grounded
Replay and does not contaminate it.
