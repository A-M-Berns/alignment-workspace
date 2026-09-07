# How authorship enters the activation event

**Status:** `ci-only`.  Lean: `AuthorityActivation.lean` (PR #92),
`OccurrenceLocalIntegrity.lean` (this round), `ReasonMediatedAuthorship.lean` (this round).

## 1. A typing defect in PR #92, repaired

PR #92's `AUTHORITY_ACTIVATED_VALUE.md` §3 declared

```
AnswerOK h r w := SessionOK(h, s) ∧ ProcessCert(h, r, w, ρ.proc) ∧ Bind(ρ.key, V)
```

with `ρ` and `V` "read from the answer event".  The generic protocol field is

```
Protocol.AnswerOK : List ℕ → Req → Warrant → Prop
```

and an `AnswerReceipt r` stores `adequate : S.AnswerOK atHistory r warrant` where
`atHistory` is the **strict prefix before the answer event** (`Authority.event_fresh :
event ∉ atHistory`).  So `AnswerOK` is evaluated at a prefix that does not contain the
event, and it takes no event argument: **it cannot see the payload**.  PR #92's prose
put `Bind(V)` somewhere it cannot be expressed.  This round repairs the typing rather
than the protocol.

## 2. The three-layer separation

| layer | object | authenticates | existing? |
|---|---|---|---|
| account / receipt | `Program.activated`, the unique `AnswerReceipt` with its `event : ℕ` and `warrant` | **which** event answered, under which warrant, at which prefix | yes — `OccurrenceIntegrity.lean`; `activated` from PR #92 |
| event / payload semantics | `payload : ℕ → Option (𝒱 × Key × Proc)` read off the authenticated history at `receipt.event`; `Bind key V` | **what** the event contained and **who** bound it | the history already carries event content (EXT authentication); `Neutral.Bind` from PR #92 |
| process / authorship certificate | `Authored β R V author D z` and `Blind β R P z` for the session, as receipts in `payload(event).proc` | **how** the payload was produced | new: `ReasonMediatedAuthorship.lean`; its meaning EXT |

The three compared alternatives:

- **Inside `AnswerOK`.**  Not expressible (§1) without changing the generic field to
  `History → ℕ → Req → Warrant → Prop`.  That is a change to `OccurrenceIntegrity.lean`'s
  protocol, propagating to every consumer, to carry an evaluation-specific fact.
  Rejected: not forced.
- **As a semantic condition on the authenticated event, outside the account.**  This is
  where the *binding* lives: `Bind` is a property of the event's content, and the
  history's event content is already external data.  Adopted for `Bind`.
- **As a derived predicate over the receipt plus the event payload.**  This is where
  *authorship* lives: it reads the receipt's `event` (which the account pins), the
  payload at that event, and the session's process receipts.  Adopted for `Authored`.

So `AnswerOK atHistory r w` keeps its generic reading — *under warrant `w`, at this
prefix, an answer to `r` is admissible* — and the evaluation-specific content sits in
a derived predicate:

```
EvalAnswered(T, h_m) :=
  activated T                                              -- account layer, LEAN
  ∧ let ρ := the unique answer receipt of T                 -- account layer
    let (V, key, proc) := payload(h_m, ρ.event)             -- event layer, EXT
    Bind key V                                              -- event layer
    ∧ ExclusiveBind: ρ.warrant is the principal role's binding warrant and
        Authorized ρ.atHistory ρ.warrant holds only for principal-produced events
                                                            -- existing field + EXT
    ∧ ReasonMediated / Blind certified by proc              -- process layer, EXT
```

**Exclusive binding uses an existing field.**  `Authority.warrant` and
`Protocol.Authorized atHistory warrant` are already in every receipt.  Typing the
principal role's *binding warrant* as the only warrant under which an evaluation answer
is `Authorized` makes `ExclusiveBind` the existing authority check plus the semantic
authentication the generic theory already leaves external.  No new field.

## 3. The activation event

```
C_n(h_m) := EvalAnswered(O_m.account o_n, h_m)  ∧  LocalLegit_n
```

| conjunct | derived from | label |
|---|---|---|
| `activated T` | the three-fate account (`Program.activated`) | LEAN |
| unique receipt, its `event`, `warrant`, `atHistory` | `Program.terminals`; `fates = {answered}` ⇒ one answer leaf | LEAN |
| `Bind key V` | event payload semantics | EXT (typed in PR #92's `Neutral`) |
| `ExclusiveBind` | `Authorized` at the receipt's prefix for the binding warrant | existing field; meaning EXT |
| `ReasonMediated`, `Blind R P` | the session's process receipts | typed here (`ReasonMediatedAuthorship.lean`); meaning EXT |
| `LocalLegit_n` | occurrence-local Integrity trace + scoped openness at every snapshot | LEAN projection (`OccurrenceLocalIntegrity.lean`) |

**Authorship is not put into generic `LegitimateEvolution`.**  It is an
evaluation-specific answer semantics, consumed by activation, and nothing in the
Integrity or openness theorems needs it.  The architecture is unchanged:

```
generic legitimacy (LocalLegit)  +  evaluation answer/authorship semantics
    →  authoritative evaluation activation C_n
```

## 4. Integrity locality (Part VI)

PR #92's `LegitimateForSegment` scopes openness but carries a global `Evolution`.  The
test trajectory: occurrence `1` vanishes from the record (exposure shrinks) while
occurrence `0`'s account propagates and its scope is open.  `Witness.no_evolution`
(**LEAN**): no global `Evolution` exists — `Conservation.exposure` forbids it.
`Witness.localLegit` (**LEAN**): the occurrence-local certificate is inhabited.

**Decision: the evaluation should activate.**  What `C_n` needs from Integrity is that
*this* occurrence's account was propagated faithfully and its receipts are authentic.
The first is the local trace; the second is the protocol's `Authorized` / `AnswerOK`
per receipt, which neither the global nor the local object supplies.  The global
`Evolution` adds propagation of *other* occurrences and monotone exposure, which are
properties of the process's whole record, not of this evaluation's authority.

The weakest object (`OccurrenceLocalIntegrity.lean`, **LEAN**):

- `Program.substOn` — substitution at exactly the live ports an account occupies;
  `substOn_eq_subst` — agrees with `subst` under a restricted total replacement.
- `LocalStep` — a fresh event, the occurrence still exposed, replacements for its own
  live ports; `LocalTrace` — a chain of them.
- `Step.toLocal`, `Evolution.toLocalTrace` — **projection**: every global step or
  evolution restricts to a local one for any occurrence exposed at its start, ending at
  the globally propagated account (`Step.toLocal_propagate`).
- `LocalLegit scope sem o` — explicit state snapshots, each `OpenAtFor scope`, with the
  occurrence's account propagated locally between consecutive snapshots.
  `LegitimateForSegment.toLocalLegit` projects PR #92's certificate to it.

The snapshots stay *full* states because the openness semantics is indexed by the whole
state (it reads carriers off the docket and accounts).  So the object is
occurrence-local in Integrity and scope-local in openness; the *other* occurrences'
accounts appear in the snapshots as data the openness semantics may read, not as
accounts that must propagate.  PR #92's phrase "occurrence-local legitimacy" was
scope-local openness over global Integrity; `LocalLegit` is the object the phrase
should have named, and `C_n` above uses it.

**Substantive caveat, stated not decided.**  A record-keeper that dropped one
occurrence is *evidence* against the authenticity of its other receipts.  That is an
evidentiary policy about the protocol's semantic authentication, which the theory
leaves external; an application may require global Integrity for that reason, and the
projection theorem says it loses nothing by doing so.  The theory's answer is that
authority of the evaluation does not *mathematically* depend on the unrelated
occurrence.

## 5. What is not established

- That `payload` is authentic, that `Authorized` for the binding warrant means
  principal-produced, that the process receipts mean reason mediation held: all EXT,
  the same class of assumption as every protocol predicate.
- Whether an application should adopt global Integrity as an evidentiary policy.
