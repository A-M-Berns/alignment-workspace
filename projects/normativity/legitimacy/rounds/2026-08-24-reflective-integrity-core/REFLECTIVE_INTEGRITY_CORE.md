# Reflective Integrity Core v1.0

Status: **specification; unregistered.** All names are provisional under
`AGENTS.md` §6. The statements below are paper derivations; each is exercised
by finite histories in `src/` and `tests/`, and none is Lean-checked or
registered. `src/ri_core.py` is a reference model, not a proof.

Tags: `[DEF]` true by representation or type · `[THM]` derived · `[ASM]` an
assumption on a parameter.

---

## 1. Scope and non-goals

Reflective Integrity is a safety property of a normative record:

```text
RI = GroundingConservation + AnswerabilityConservation
```

It says that every normative event in the record was licensed by the record
that preceded it, and that every custody episode the record ends is either
answered or visibly outstanding. It is not a progress theorem: nothing here
bounds how long a root may stay live, and nothing asserts eventual closure.

Out of scope, with hooks in §32: residual liability and release, transfer
consent, principal competence, protocol semantics, relational answerability,
fairness, and normative correctness. A licensed custody assignment is not a
correct one.

---

## 2. Meta-Stability

**(MS)** These are metatheoretic constants, invariant along every trajectory
and subject only to conservative extension — a new constructor gets a new
clause, and every existing term keeps its clauses verbatim:

> Time (linear, `tau` injective); the grammar of `V`; `StandingEffect`,
> `NormEffect`, `targets`, `fresh`, `delta`, `applyEffect`; `CommitmentRole`;
> `SchemaCode` with `[[.]]_S`; `DemandCode` with `[[.]]_D`; `Disposes`, `MINT`,
> `succ`, `Live`/`Due`/`Closed`, `ContinuityOK`, `Digest`.

No substantive normative correctness is encoded in any of them.

---

## 3. Standing Locality

**(SL)** `standing(V_N, x) := V_N(x)`, and `V_N` is the sole component of the
normative view. Protocol, schema and applicability state may govern the
validity of future events; none of it may enter the semantic value of existing
standing.

The stratification line: `CommitmentRole` is meta-level and two-valued;
`content : ObjTerm` is object-level and opaque. A meta-level `content` would
make §31 impossible; an object-level role would let an ontology change alter
how the stance fold reads existing standing, violating MS.

---

## 4. Seed / genesis

The seed is a theorem parameter, not a store.

```text
Seed = ( Std_0 : StandingId ->fin StandingState , Roots_0 : Finset AnsRoot )
```

`WFSeed(Seed)` holds when:

| | |
|---|---|
| **Z1** | `dom(Std_0)` finite; `forall x. status_0(x) in {Active, Suspended}` |
| **Z2** | `forall x in dom(Std_0). pred_0(x) = {}` |
| **Z3** | `forall x in dom(Std_0). exists! q in Roots_0. subject(q) = x` |
| **Z3'** | `forall q in Roots_0. subject(q) in dom(Std_0)` |
| **Z4** | `forall q in Roots_0. origin(q) = Genesis and creditor(q) = Stage(P_0, 0) and tau(q) = 0` |
| **Z5** | ids in `Std_0` and `Roots_0` pairwise distinct |
| **Z6** | `L_0 = R_0 = N_0 = {}` |

Z3 and Z3' together make `subject : Roots_0 -> dom(Std_0)` a bijection. Z6 says
the trajectory begins with three empty ledgers: the seed supplies standing and
roots, and nothing else.

Where bootstrapping bottoms out. Grounding Conservation guarantees that every
event has a `tau`-well-founded account terminating at the seed; it makes no
claim about the seed. The choice is an axiomatic seed or an empty trajectory,
and no self-licensing genesis event is manufactured. `[DEF]`

The seed is not privileged going forward: seed standing carries ordinary roots,
may be superseded, transferred and suspended, and its episodes obey every rule
below.

**Degenerate instantiation.** If `Std_0` contains no `PAuth` object, no Norm
step is ever well-formed, the trajectory holds only settlements, reasons and
responses, and every theorem below holds. `[THM]`

---

## 5. Settlement, Reason and Normative stores

```text
S_t = ( L_t , R_t , N_t )     append-only; no delete; tau injective and strictly increasing
```

| store | content |
|---|---|
| `L` Settlement Ledger | settlement records; persistent, and settlements do not defease |
| `R` Reason Ledger | `ReasonOcc` — immutable reason occurrences |
| `N` Normative Record | `NormEvent` and `Response` |

```text
settlement  !=  reason  !=  normative uptake
```

Everything else is derived and never stored: `effect(a)`, `basis(a)`,
`Digest(a)`, `Roots_t`, `CurrentEpisode`, `HasCustody`, `Live`/`Due`/`Closed`,
`succ_t`, `Desc*_t`, `ContinuityOK`.

---

## 6. `SystemStep`

```text
SystemStep ::= Settle (s : Settlement) | Reason (e : ReasonOcc)
             | Norm (a : NormEvent)    | Respond (rho : Response)
```

`tau(step_t) = t + 1`, so `tau` is injective. `[DEF]`

```text
WFStep(S_t, Settle s)    <=> id(s) fresh; refs(s) subset ids(L_t)
                             S_{t+1} = (L_t + s, R_t, N_t)
WFStep(S_t, Reason e)    <=> id(e) fresh; s_V(e) subset_fin V; s_L(e) subset ids(L_t)
                             S_{t+1} = (L_t, R_t + e, N_t)
WFStep(S_t, Norm a)      <=> WF(a)   (G1-G6, §14)
                             S_{t+1} = (L_t, R_t, N_t + a); Roots_{t+1} gains MINT(a)
WFStep(S_t, Respond rho) <=> id(rho) fresh; roots(rho) subset ids(Roots_t);
                             cited(rho) subset ids(NormEvents_t)
                             S_{t+1} = (L_t, R_t, N_t + rho)
```

Four constructors, and no fewer. `Respond` cannot fold into `Norm` — it has no
certificate, no schema and no effect, and merging them would break Response
Non-Authority. `MINT` cannot be a separate step — a state in which a
disposition has occurred and its successor root has not yet been issued would
be a state at which Episode Uniqueness fails.

**No validity check on responses.** Whether `rho` completes anything is decided
by the frozen demand predicate, never by the step. An invalid response is an
appended record that fails `[[d]]_D`.

---

## 7. Reason representation

```text
ReasonOcc e = (id, s_V : Finset V, s_L : Finset SettleId, t : V, tau : Time)
V ::= Atom p | Neg V | App(sigma, c, n) | Inst(e, sigma)
Enabled_{B,L}(e) <=> s_V(e) subset B and s_L(e) subset L
```

The four constructors above are the whole grammar: an effect is never named in
the reason language. Historically particular effects are reached by schema
selectors reading rigid historical objects already in the ledgers —
canonically `Inst(e, sigma)` in the conclusion and `e in basis(x)` in the
selector. Appending a reason never changes any existing reason's enabledness,
any stance, or any root.

---

## 8. Inference-step licensing provenance

```text
steps : Derivation -> Finset StandingId
```

```text
G3(a)  <=>  forall s in steps(D_a).  Std_{<tau(a)}(s) = (Active, _, PAuth _)
```

> **RI checks that inference steps were licensed. RI does not prove them
> sound.**

The payload code of a step licence is never read: `[[.]]_S` is applied to
exactly one object per event, the one named by `schemaRef(a)` (§14). No
inference interpreter is part of any theorem here, and the practical-schema
interpreter is not made to serve as one. The typing distinction is which
clause reads the code, and that is the whole of it.

---

## 9. Parametric practical-schema interface

RI is parametric over `(SchemaCode, [[.]]_S)`.

```text
SchemaCode : Type
[[.]]_S    : SchemaCode -> (Match x PreState -> NormEffect)      -- partial
```

| | assumption | used by |
|---|---|---|
| **S1** | `SchemaCode` and `[[.]]_S` are meta-stable (MS); conservative extension only | Digest Stability, non-retroactivity |
| **S2** | `[[sigma]]_S` is a partial function: fixed `(sigma, wit, P)` gives one `NormEffect` | Effect Determinacy |
| **S3** | read-only in `P` — it is a function *into* `NormEffect`, and cannot write | TargetCoverage, SL |
| **S4** | the output is a well-typed `NormEffect` | soundness of the fold |
| **S5** | `P` is the strict pre-state including `tau`; no dependence on `>= tau` | Digest Stability |
| **S6** | the interpreter does not choose ids: fresh ids are `fresh_i(alpha, tau)` (§13) | Effect Determinacy, EP |

Nothing about expressiveness is assumed. `SchemaCode = {}` is admissible and
gives the degenerate instantiation of §4: the foundational theorem contains no
expressiveness judgment. `[THM]`

---

## 10. Parametric episode-demand interface

```text
DemandCode  : Type
Digest       = ( tau, author, effect, disposed : Finset AnsRootId )
CitedDigest(rho_vec) : ids(union_{rho} cited rho) -> Digest
[[.]]_D     : DemandCode -> (AnsRoot x Multiset Response x CitedDigest -> Prop)
```

Two structural assumptions. They are the counterpart of S1-S6, and they are
what four of the eight main clauses actually consume.

**D1 — Monotonicity.** `[ASM]` For every `d`, `q`, every multiset inclusion
`rho_vec <= rho_vec'`, and every pair of cited-digest maps with
`delta subset delta'` as graphs — that is, `dom delta subset dom delta'` and
they agree on `dom delta`:

```text
[[d]]_D (q, rho_vec, delta)  =>  [[d]]_D (q, rho_vec', delta')
```

The graph-inclusion hypothesis is exactly what Digest Stability (§18) supplies:
`rho_vec <= rho_vec'` gives `CitedDigest(rho_vec) subset CitedDigest(rho_vec')`,
because each cited event's digest is a function of its own strict prefix and
that prefix never changes. Without the agreement condition, D1 would be a claim
about arbitrary reinterpretations of history and would be false.

**D2 — Disposition gating.** `[ASM]` For every `d`, `q`, `rho_vec`, `delta`:

```text
[[d]]_D (q, rho_vec, delta)  =>  exists rho in rho_vec. exists aid in cited(rho) cap dom(delta).
      id q in roots(rho)  and  id q in delta(aid).disposed  and  delta(aid).tau < tau(rho)
```

A demand may be satisfied only by evidence that a real disposition of this root
has already occurred and is represented by a digest the responder cited.

**[THM] Closure needs a disposer.** `Closed_t(q) => exists a in NormEvents_t.
Disposes(a, q)`.
*Proof.* `Closed_t(q)` unfolds to `[[demand q]]_D` at
`(q, Responses_t(q), CitedDigest(...))`. D2 yields `aid` in the domain of that
map; the Respond step condition puts `aid in ids(NormEvents_t)`; and
`delta(aid) = Digest(a)` with `id q in disposed(a)` is by definition
`Disposes(a, q)`. ∎

Neither assumption is normative correctness. D1 says answering is not undone by
answering more; D2 says an episode is not closed before it has ended.

`AccountForSuccession` is the built-in value and satisfies both by inspection —
it is the existential of D2's own shape.

---

## 11. Standing ontology

```text
StandingId      : opaque
CommitmentRole ::= StanceBearing | NonStanceBearing
Status         ::= Active | Suspended | Terminated NormEventId
Payload        ::= PCmt (role : CommitmentRole, content : ObjTerm)
                 | PAuth SchemaCode
                 | PForce (commitRef : StandingId, schemaRef : StandingId, compiledClause : Clause)
                 | PProto ObjTerm
StandingState   = ( status : Status , pred : Finset StandingId , payload : Payload )
NormativeView   = StandingId ->fin StandingState
```

The three fields above are the whole of `StandingState`. Custody, actual stance
and operative force are derived: custody from the unique current episode
(§15.1), which is what makes §21 a theorem rather than a convention, and stance
and force as folds over the normative view.

```text
Std_t = fold applyEffect Std_0 over { effect(a) : a in NormEvents_{<=t} } in tau-order
B^_t  = { content k : exists x. Std_t(x) = (Active, _, PCmt (StanceBearing, k)) }
O_t   = { compiledClause p : exists x. Std_t(x) = (Active, _, PForce p) }
```

No core definition reads protocol standing — not `WF`, not
`targets`/`delta`/`Disposes`/`MINT`, not `[[.]]_S` or `[[.]]_D`, not the fates,
not `succ`/`ContinuityOK`, not GC or AC. Uniqueness of an active `PProto` is
not assumed and may fail in either direction; an application layer may
interpret them. Consequently an existing root reads no protocol state
whatsoever. `[DEF]`

---

## 12. Standing-effect interpreter

```text
StandingEffect ::= Create    (K : List Payload)
                 | Supersede (X : Finset StandingId, K : List Payload)
                 | SetStatus (X : Finset StandingId, s : Active | Suspended)
NormEffect     ::= Standing StandingEffect | Transfer (x : StandingId, to : PrincipalId)

targets(Create _) = {}        targets(Supersede X _) = X      targets(SetStatus X _) = X
targetsN(Standing alpha) = targets alpha        targetsN(Transfer x _) = {x}
```

Derived forms: `Revoke x = Supersede({x}, [])`; protocol amendment and force
replacement are `Supersede` on the relevant object. These three constructors are
the whole of `StandingEffect`, so every change to a protocol or an authority is
a supersession with the lineage `pred(y) = X` records, and custody moves only
through the `Transfer` constructor of `NormEffect`.

### 12.1 The locality-typed interpreter

```text
delta : (alpha : StandingEffect) -> (targets alpha -> StandingState)
                                 -> (targets alpha -> StandingState) x (fresh alpha -> StandingState)

applyEffect V (Standing alpha) = V (+) pi_1(delta alpha ...) (+) pi_2(delta alpha ...)
applyEffect V (Transfer _ _)   = V
```

Clauses — the only place standing is written:

```text
Create K      : pi_1 = {} ;                                       pi_2 = fresh_i |-> (Active, {}, K_i)
Supersede X K : pi_1 = x |-> (Terminated a, pred x, payload x) ;  pi_2 = fresh_i |-> (Active, X, K_i)
SetStatus X s : pi_1 = x |-> (s, pred x, payload x) ;             pi_2 = {}
```

`pred(y) = X` for every `y in fresh(Supersede X K)` is a clause shape, not a
checked condition; `payload` and `pred` are read, never rewritten. `[DEF]`

### 12.2 Preconditions (G6)

For `Supersede X _`, `SetStatus X _` and `Transfer x _`:

```text
targetsN(effect a) subset dom(Std_{<tau(a)})   and   forall y in targetsN(effect a). status_{<tau(a)}(y) != Terminated
```

Domain membership is the first conjunct because `delta` reads `pred` and
`payload` off each target.

### 12.3 TargetCoverage

```text
StandingChanges(a, x) :<=> standing(Std_{<=tau(a)}, x) != standing(Std_{<tau(a)}, x)
```

**[THM] Standing Locality (frame lemma).** For `alpha : StandingEffect`,
`x notin targets alpha ∪ fresh alpha => standing(applyEffect V (Standing alpha), x) = standing(V, x)`.
*Proof.* The override domain is contained in `targets alpha ∪ fresh alpha` by
the type of `delta`, and a map override is the identity off its domain. ∎

**[DEF] Transfer Neutrality.** `applyEffect V (Transfer _ _) = V`: the
interpreter has no clause to write with.

**[THM] TargetCoverage.** `StandingChanges(a, x) => effect(a) = Standing alpha
and x in targets alpha ∪ fresh alpha`.

---

## 13. Freshness

```text
fresh(Create K)      = fresh(Supersede _ K) = |K|          fresh(SetStatus _ _) = 0
fresh_i(alpha, tau)  = tag(tau, i)
MINT root ids        = rootTag(tau, j)
```

| | assumption |
|---|---|
| **F1** | `tag` is injective on `(tau, index)` |
| **F2** | `range(tag) cap dom(Std_0) = {}` |
| **F3** | `rootTag` is injective on `(tau, index)`, and `range(rootTag) cap ids(Roots_0) = {}` |

**[THM] Fresh allocation.** `fresh(effect a) cap dom(Std_{<tau(a)}) = {}`, and
the ids in `fresh(effect a)` are pairwise distinct.
*Proof.* `dom(Std_{<tau(a)}) = dom(Std_0) ∪ union_{tau(b) < tau(a)} fresh(effect b)`
by the fold. F2 excludes the seed part. For the rest, `tau` is injective on the
trajectory, so `tau(b) != tau(a)`, and F1 makes `tag(tau(b), j) != tag(tau(a), i)`.
Pairwise distinctness of siblings is F1 at fixed `tau`. ∎

The same argument at `rootTag` gives fresh, pairwise-distinct root ids, which
is what AC(i) and Episode Uniqueness consume.

`schemaRef(a)` lies in `dom(Std_{<tau(a)})` by G4, so the theorem also gives
`schemaRef(a) notin fresh(effect a)`: no event can be licensed by standing it
creates. Self-licensing is excluded by the allocator, not by a side condition.

---

## 14. Normative-event well-formedness

```text
NormEvent a = ( id , cert : (D : Derivation, schemaRef : StandingId, wit : Match) ,
                author : PrincipalId , tau : Time )
PreState_{<tau} := (L_{<tau}, R_{<tau}, N_{<tau}, tau)
basis(a)        := ReasonLeaves(D_a)
```

`WF(a)` is a conjunction evaluated **in this order**, and the order is the
definition's dependency order:

| | clause |
|---|---|
| **G1** | `id(a) notin ids(N_{<tau(a)})`; `concl(D_a) in V` |
| **G2** | `ReasonLeaves(D_a) subset ids(R_{<tau(a)})`, each `Enabled_{B^_{<tau(a)}, L_{<tau(a)}}` |
| **G3** | `forall s in steps(D_a). Std_{<tau(a)}(s) = (Active, _, PAuth _)`  (§8) |
| **G4** | `Std_{<tau(a)}(schemaRef a) = (Active, _, PAuth sigma)` |
| | — `effect(a) := [[sigma]]_S (wit a, PreState_{<tau(a)})`, defined exactly here — |
| **G5** | `[[sigma]]_S (wit a, PreState_{<tau(a)})` is defined, and `match(pattern(sigma), wit a)` |
| **G6** | the preconditions of `effect(a)` hold (§12.2) |

`effect(a)` is a partial function of the event, total on `NormEvents_t` because
`WFStep` admits nothing that fails G4 and G5. It is defined by strong recursion
on `tau`, well-founded because `tau` is a strict order on a finite set, and
because G4 resolves `schemaRef` in the strict pre-state before any clause
mentions `effect(a)`. `[DEF]`

**[DEF] Historically frozen.** `WF(a)` is step-local and evaluated once, at
`tau(a)`, against the strict prefix. `S_{<tau(a)}` never changes, so `WF(a)` is
never re-decided and later events cannot invalidate earlier ones.

**Underdetermination is permitted.** Two active `PAuth` objects may match the
same conclusion and form different effects; which fires is fixed by the event's
`schemaRef`, and that choice is itself answerable, since every `PAuth` object
carries its own custody episode. `[DEF]`

---

## 15. Answerability roots and derived custody

```text
Creditor  = Stage (PrincipalId x Time)
Origin   ::= Ev NormEventId | Genesis
AnsRoot q = ( id, creditor : Creditor, debtor : PrincipalId, subject : StandingId,
              demand : DemandCode, origin : Origin, tau : Time )      -- every field immutable
```

> **`AnsRoot = CustodyEpisode`.** Custody is the answerability baton: which
> principal is presently charged with carrying `subject` through its next
> accountable transition. It is not ownership, endorsement, authority, causal
> control, residual liability, or authorship. `PrincipalId` is thin.

### 15.1 Custody is derived

```text
CurrentEpisode_t(q) :<=> Live_t(q) and not Due_t(q)
HasCustody_t(P, x)  :<=> exists! q. CurrentEpisode_t(q) and subject q = x and debtor q = P
```

### 15.2 Disposition is episode-relative

```text
Disposes(a, q) <=> CurrentEpisode_{<tau(a)}(q)
                   and subject q in targetsN(effect a)
                   and effect a in { Standing (Supersede _ _) , Transfer _ _ }
```

| effect | disposes the subject's episode? |
|---|---|
| `Supersede` of the subject | yes |
| `Transfer` of the subject | yes |
| `SetStatus(_, Suspended)` / `SetStatus(_, Active)` | no — suspension does not end the episode |
| `Create` | no |
| `Settle` / `Reason` / `Respond` steps | no |

`author(a) = debtor(q)` is not required: a third party may validly dispose
standing entrusted to another principal. The `CurrentEpisode` conjunct selects
which episode, not who acted.

**[DEF] Disposition uniqueness.** After the first disposing `a`, `q` is no
longer current, so the first conjunct fails for every later event.

---

## 16. Transfer

```text
Transfer (x : StandingId) (to : PrincipalId)
```

Singleton, with precondition `x in dom(Std_{<tau})` and
`status_{<tau}(x) != Terminated`. Six properties, all `[DEF]`: standing is
untouched (§12.1); `q_A` is disposed (§15.2); `q_A` becomes `Due` (§19); `q_B`
is minted with debtor `B` (§17); the edge `q_A -> q_B` exists (§22); and
**admissibility via authorization** (§9, G3/G4).

> **A valid custody assignment is not recipient consent.** Admissibility is
> what the authorizing schema confers. Whether `B` accepted is a legitimacy
> question, and it is deferred (§32). Nothing in core RI records or requires
> acceptance.

---

## 17. Minting

```text
episodes(a) = { (y, author a) : y in fresh alpha }   when effect a = Standing alpha
            ∪ { (x, B) }                            when effect a = Transfer x B

MINT(a) = for each (z, P) in episodes(a), in index order, one root
          ( rootTag(tau a, j), creditor = Stage(author a, tau a), debtor = P,
            subject = z, demand = AccountForSuccession, origin = Ev (id a), tau = tau a )
Roots_t = Roots_0 ∪ union_{a in NormEvents_{<=t}} MINT(a)
```

| event | disposes | mints |
|---|---|---|
| `Create K` | nothing | one per `y in fresh`, debtor `= author` |
| `Supersede X K` | the current episode of every `x in X` | one per `y in fresh`, debtor `= author` |
| `SetStatus` | nothing | nothing |
| `Transfer x B` | the current episode of `x` | one, subject `x`, debtor `B` |

Creditor is `Stage(author a, tau a)` uniformly; §33 says what that buys.
Debtor of successor roots is `author(a)` uniformly: inheriting the disposed
episode's debtor is ill-defined for merges, which have two predecessors and two
custodians, and the author is well-defined and carries no extra field.

Every standing object — `PCmt`, `PAuth`, `PForce`, `PProto` — is minted under
the same rule. No privileged commitment semantics.

---

## 18. Responses and frozen digests

```text
Response rho    = ( id, roots : Finset AnsRootId, cited : Finset NormEventId, tau : Time )
Responses_t(q)  = { rho in N_t : id q in roots rho }
Digest(a)       = ( tau(a), author(a), effect(a), disposed(a) )
disposed(a)     = { id q : Disposes(a, q) }
```

**[THM] Digest Stability.** `Digest(a)` computed at any `t >= tau(a)` is the
same value.
*Proof.* Each component is a function of `S_{<tau(a)}` alone: `effect` by S5,
and `disposed` through `CurrentEpisode_{<tau(a)}` and `effect`. `S_{<tau(a)}`
is an append-only prefix and never changes. ∎

Digest is derived, not stored; freezing is the typing decision that makes it
so.

> Completion may inspect the root, the responses naming it, and the frozen
> digests of the events those responses explicitly cite — nothing else. It
> never quantifies over `N_t`.

| required property | mechanism | level |
|---|---|---|
| frozen | `[[.]]_D` is meta-stable and the root's `demand` is fixed at minting | `[DEF]` |
| monotone in responses | D1 | `[ASM]` |
| Response Non-Authority | that `a` disposes `q` comes from `Digest(a)`, computed from `a`'s certificate and the frozen prefix — never from the response | `[DEF]` |
| later unrelated events cannot change an existing response's validity | Digest Stability, and the evaluator sees nothing outside `cited(rho_vec)` | `[THM]` |
| an invalid cited event cannot become valid retroactively | `cited(rho) subset ids(NormEvents_t)` and every event in `N` is `WF`, so `Digest` is defined and stable | `[THM]` |

---

## 19. `Closed` / `Live` / `Due`

For `q in Roots_t`:

```text
Closed_t(q) <=> [[demand q]]_D ( q, Responses_t(q), CitedDigest(Responses_t(q)) )
Live_t(q)   <=> not Closed_t(q)
Due_t(q)    <=> Live_t(q) and exists a in NormEvents_t. Disposes(a, q)
```

**[DEF] Trichotomy.** For `q in Roots_t`, exactly one of `Closed_t(q)`,
`Live_t(q) and not Due_t(q)`, `Due_t(q)`. The quantifier is `Roots_t`: a root
value that was never issued is in none of the three, and no clause below claims
otherwise.

```text
Live and not Due  =  episode still in accountable custody   (permitted indefinitely)
Due               =  episode ended; its account is now owed
Closed            =  episode ended and has been accountably answered
```

`Due` is not a deadline violation, and no temporal bound is part of RI.

**[THM] Fate Monotonicity.** Under D1 and D2, the fate of `q in Roots_t` moves
only forward along `(Live and not Due) -> Due -> Closed`, and never backwards.
*Proof.* `Live and not Due -> Due` needs a disposing event, and `N` is
append-only, so it never un-happens. `Due -> Closed` is a Respond step; by D1
and Digest Stability, `Closed` once established persists. `(Live and not Due)
-> Closed` in one step is excluded by D2, which requires a disposer already in
the record. ∎

**[THM] Closure passes through `Due`.** If `q` is closed at some `t` then it is
`Due` at `tau(a)`, where `a` is its unique disposer.
*Proof.* At `t = tau(a)`, D2 would need a response `rho` with
`tau(a) < tau(rho) <= t`; there is none. So `q` is live and disposed at
`tau(a)`, which is `Due`. ∎

---

## 20. Episode Uniqueness

**(EP)** For every `t` and every `x in dom(Std_t)`:

```text
status_t(x) != Terminated  <=>  exists! q. CurrentEpisode_t(q) and subject q = x
```

**[THM]** Induction on `t`.

*Base.* By Z3 and Z3', `subject` is a bijection `Roots_0 -> dom(Std_0)`. By Z6,
`N_0 = {}`, so `Responses_0(q) = {}` and no event disposes anything; by D2,
`Closed_0(q)` is false, so every seed root is `Live and not Due`, hence current.
By Z1 no seed status is `Terminated`. Both directions follow, and uniqueness is
Z3's `exists!`.

*Step.* `Settle` and `Reason` change no root, fate or standing. `Respond` moves
a root only `Due -> Closed`: if `q` were current at `t` and closed at `t+1`,
D2 would give a disposer in `NormEvents_{t+1} = NormEvents_t`, making `q` `Due`
at `t` and so not current. `Norm a` by cases on `effect(a)`:
`Create K` takes each fresh `y` from 0 to 1 episodes, and §13 makes each `y`
new; `Supersede X K` finds each `x in X` non-terminated by G6, hence with a
unique current episode by IH, disposes it (1 -> 0) exactly as `status`
becomes `Terminated`, and mints one episode per fresh `y` (0 -> 1);
`SetStatus` changes neither side; `Transfer x B` disposes the unique current
episode of `x` and mints exactly one with subject `x` (1 -> 1). ∎

---

## 21. Custody Locality

**[THM]** If `HasCustody_t(A, x)`, `HasCustody_{t'}(B, x)`, `A != B` and
`t < t'`, then some `a` with `t < tau(a) <= t'` has `effect(a) = Transfer(x, ·)`.
*Proof.* By EP the current episode for `x` is unique at each time, so it
changed. Episodes end only by disposition and begin only by minting.
`Supersede` on `x` ends `x`'s episode and mints nothing with subject `x`, and
terminates `x` besides. `Create` and `SetStatus` neither begin nor end an
episode for an existing `x`. Only `Transfer` both ends one and begins one with
subject `x`. ∎

> Deriving custody made the invariant stronger than a field could: a field
> could be written by any `delta` clause targeting `x`, and the derived view can
> change only through the constructor above — as a theorem.

---

## 22. Successor DAG

```text
succ_t(q)   = { q' in MINT(a) : Disposes(a, q), tau(a) <= t }
Desc*_t(q)  = least set containing q and closed under succ_t
```

| disposing effect | `succ_t(q)` |
|---|---|
| `Supersede X [k_1..k_n]` | `{q_{y_1}, ..., q_{y_n}}` for every `q` with subject in `X` — merges converge |
| `Supersede X []` | `{}` |
| `Transfer x B` | `{q_B}` |

**[DEF] Strictly time-forward.** `q' in succ_t(q) => tau(q') > tau(q)`, so
`Desc*_t(q)` is finite and the DAG is well-founded on `tau`. Since
`succ_t(q) subset Roots_t`, `Desc*_t(q) subset Roots_t` for `q in Roots_t`.

**[DEF] Key lemma.** `Live_t(q) and not Due_t(q) => succ_t(q) = {} =>
Desc*_t(q) = {q}`, because a successor requires a disposing event and `not Due`
says there is none.

No edge labels. `Supersede X K` terminates all of `X` and issues all of `K`, so
there is no partial custody to apportion; scope narrowing is a fact about
content, not about the graph.

---

## 23. `ContinuityOK`

For `q in Roots_t`:

```text
ContinuityOK_t(q) <=> ( Live_t(q) and not Due_t(q) )
                    or ( Closed_t(q) and forall q' in succ_t(q). ContinuityOK_t(q') )
```

Well-founded on `tau` by §22. This is not an invariant of the trajectory; §24
says what is.

---

## 24. Due-Witness

**[THM] Due-Witness.** For every `t` and every `q in Roots_t`:

```text
not ContinuityOK_t(q)  <=>  exists r in Desc*_t(q). Due_t(r)
```

*Proof.* Well-founded induction on `q` along `succ_t`, which is strictly
`tau`-forward. By trichotomy exactly one case applies.

- `Due_t(q)`. Both disjuncts of `ContinuityOK` fail, so the left side holds;
  and `q in Desc*_t(q)` witnesses the right.
- `Live_t(q) and not Due_t(q)`. The first disjunct holds, so the left side
  fails; by the key lemma `Desc*_t(q) = {q}` and `not Due_t(q)`, so the right
  fails.
- `Closed_t(q)`. Then `ContinuityOK_t(q) <=> forall q' in succ_t(q).
  ContinuityOK_t(q')`. By IH each of those is `not exists r in Desc*_t(q').
  Due_t(r)`. Hence `not ContinuityOK_t(q) <=> exists q' in succ_t(q). exists r
  in Desc*_t(q'). Due_t(r)`. Since `Desc*_t(q) = {q} ∪ union_{q'} Desc*_t(q')`
  and `q` is `Closed` hence not `Due`, that is exactly `exists r in Desc*_t(q).
  Due_t(r)`. ∎

The statement holds unconditionally — from the definitions alone, in any state,
with no appeal to GC or AC. It is asserted of issued roots only: for a value
outside `Roots_t` both sides are false and the biconditional says nothing.

Neither `forall q. ContinuityOK_t(q)` nor `forall q. ContinuityOK_t(q) or
Due_t(q)` is claimed. Both are false: `q_0` `Closed` with `q_1 in succ(q_0)`
`Due` refutes each.

---

## 25. No Invisible Discontinuity

**[THM]** Under `Good(S_t)`: if `not ContinuityOK_t(q)` for `q in Roots_t`,
then the witness `r` of §24 satisfies `r in Roots_u` for every `u >= t` — roots
never vanish, by AC(i) — and `r`'s fate can change only to `Closed` (Fate
Monotonicity), which is gated by the frozen, local, monotone contract of §10
and §18.

> An answerability discontinuity cannot be invisible. It terminates in an
> explicit `Due` witness that cannot be deleted and can be discharged only
> through the frozen demand interface.

No eventual closure is asserted; §30 is where that lives.

---

## 26. Grounding Conservation

```text
GC(S_t) <=> forall a in NormEvents_t. WF(a)
```

| property | mechanism | level |
|---|---|---|
| immutable reason ancestry | `R` append-only; `basis(a) := ReasonLeaves(D_a)`, no stored field | `[DEF]` |
| strict pre-state citation | G2, G3, G4 range over `_{<tau(a)}` | `[DEF]` |
| no self-grounding | G1: `id(a) notin ids(N_{<tau(a)})` | `[DEF]` |
| no self-licensing | G4 resolves `schemaRef` in the strict pre-state; F1-F2 make fresh ids disjoint from it (§13) | `[THM]` |
| no post-hoc basis laundering | there is no basis field to write | `[DEF]` |
| bottoms out | at the seed (§4) | `[DEF]` |

---

## 27. Answerability Conservation

```text
AC(S_t) <=> (i)   Roots_t monotone in t; no root is removed
            (ii)  Closed_t(q) <=> [[demand q]]_D (q, Responses_t q, CitedDigest ...),
                  with the demand frozen, local and satisfying D1 and D2
            (iii) MINT applied at every Norm step
            (iv)  Response Non-Authority
            (v)   no delete on L, R or N
            (vi)  EP (§20)
```

There is no third conservation law: TargetCoverage is §12.3's theorem, and the
force projection is §11's fold.

---

## 28. Local preservation by step kind

```text
Good(S) :<=> GC(S) and AC(S)          (SL is a meta-side-condition, §3, not a state predicate)
```

**[THM] L1 (Settle).** Only `L` grows. `Std`, `Roots`, all fates and all
digests are unchanged, and `WF(a)` for `a in N_t` is frozen.

**[THM] L2 (Reason).** Only `R` grows. `B^_t` is a projection of `Std_t` and so
is unchanged; no existing occurrence changes enabledness; no root, fate or
digest changes.

**[THM] L3 (Norm).** `WF(a)` gives GC. AC: (i) `Roots` grows and never shrinks;
(ii) `Closed` for existing roots is unchanged, since `Responses` did not grow
and the digests of previously cited events are stable; (iii) `MINT` is applied
by the step; (vi) EP by §20. Existing roots may move `(Live and not Due) ->
Due` if `a` disposes them, which is the permitted direction.

**[THM] L4 (Respond).** GC is untouched — no reason, no certificate. AC: (i)
`Roots` unchanged; (ii) `Responses_t(q)` grows for `q in roots(rho)` and D1
makes `Closed` only gain; (iv) preserved by the type of `Response`, which
carries ids only; (vi) EP preserved, because the only fate change is `Due ->
Closed`, which removes a non-current episode and cannot create a second current
one.

**[THM] Local Preservation.** `Good(S_t) and WFStep(S_t, step) => Good(S_{t+1})`
for every constructor, hence for arbitrary well-formed interleavings.

---

## 29. Main theorem

**THEOREM (Reflective Integrity).** Assume MS, SL, S1-S6, D1-D2, F1-F3, and
`tau` injective and strictly increasing along the trajectory. If
`WFSeed(Seed)` and `WFStep(S_t, step_t)` for all `t`, then for all `t`:

| | |
|---|---|
| **(1)** | `Good(S_t)` — that is, `GC(S_t) and AC(S_t)` |
| **(2)** | `forall q in Roots_t.` exactly one of `Closed_t q`, `Live_t q and not Due_t q`, `Due_t q` |
| **(3)** | `forall q in Roots_t. not ContinuityOK_t q <=> exists r in Desc*_t q. Due_t r` |
| **(4)** | `forall q in Roots_t, u >= t.` the fate of `q` at `u` is `>=` its fate at `t` in `(Live and not Due) < Due < Closed` |
| **(5)** | `forall x in dom(Std_t). status_t x != Terminated <=> exists! q. CurrentEpisode_t q and subject q = x` |
| **(6)** | `HasCustody_t(A,x) and HasCustody_{t'}(B,x) and A != B and t < t' => exists a. t < tau a <= t' and effect a = Transfer x ·` |
| **(7)** | `StandingChanges(a,x) => effect a = Standing alpha and x in targets alpha ∪ fresh alpha` |

No clause bounds how long a root may remain `Live and not Due`, or `Due`.

**Effect Determinacy.** `effect(a)` is the deterministic result of the licensed
practical schema named by `schemaRef(a)` and the strict pre-state, by S2 and
S6. `[THM]`

Base case: `Good(S_0)` follows from `WFSeed` — GC vacuously by Z6, AC from
Z1-Z6 and D2 as in §20. Step: §28.

---

## 30. Optional liveness under FAIR

Separately, and never inside `Good`:

```text
(FAIR)  If Due_t(q) then some principal authors a response satisfying
        [[demand q]]_D for q within finitely many steps.
```

**[THM under FAIR]** `Due_t(q) => exists u > t. Closed_u(q)`.
**[THM under FAIR]** `forall q, exists u >= t. ContinuityOK_u(q)` or some
descendant of `q` is `Due` at `u`.

FAIR is not derivable from §§2-29. Indefinite `Live and not Due` — suspension,
continued custody — and temporary `Due` are RI-conformant.

---

## 31. Changing-ontology boundary

In scope: radical change of object-level and normative content, because
`content : ObjTerm` is opaque to every meta-rule.
`Supersede({x}, [PCmt(role, content_new)])` works with `pred(y) = {x}` fixing
identity-based lineage, `q_x` disposed, a response citing the event, and `q_y`
minted. No semantic-equivalence judgment occurs anywhere. `[DEF]`

> **Preserve historical reference, not semantic representation.**

Old standing remains historically referable by identity, `pred` and `basis`,
even when the current reasoner no longer natively uses its ontology.

Out of scope, excluded by MS: mutation of the metalanguage. Conservative
extension of `SchemaCode`, `DemandCode`, `Payload` and `V` is permitted;
rewriting is not.

---

## 32. Deferred machinery

| deferred | hook, needing no new state |
|---|---|
| residual liability and release | a `LiablePrincipals_t(q) ⊇ {debtor q}` view over the successor DAG |
| transfer acceptance and consent | an admissibility side-condition on the `PAuth` schemas that form `Transfer` |
| response authorship attribution | a field on `Response`; the demand already reads `id q in roots rho` |
| `IssuanceStanding`, `Nexus`, `AnswerableTo`, `OwesAnswerTo` | relational views over roots; `OwesAnswerTo` uses `Due`, not `Live` |
| challenge and review roots | new `DemandCode` values, by conservative extension |
| protocol semantics | `PProto` objects; core RI reads none |
| principal competence | a condition on `PrincipalId`, which is thin here |
| progress and fairness | §30 |
| normative correctness | outside RI entirely |

Every conjunct of `Good` and every clause of §29 is discharged without a
release relation. `[THM]`

---

## 33. Exact minimal signature

```text
Time : LinearOrder     StandingId, PrincipalId, NormEventId, AnsRootId, ObjTerm, Clause : Type
CommitmentRole ::= StanceBearing | NonStanceBearing
Status         ::= Active | Suspended | Terminated NormEventId
Origin         ::= Ev NormEventId | Genesis
Creditor        = Stage (PrincipalId x Time)
V              ::= Atom p | Neg V | App(sigma,c,n) | Inst(e,sigma)

Payload        ::= PCmt (CommitmentRole x ObjTerm) | PAuth SchemaCode
                 | PForce (StandingId x StandingId x Clause) | PProto ObjTerm
StandingState   = (status : Status, pred : Finset StandingId, payload : Payload)
NormativeView   = StandingId ->fin StandingState

StandingEffect ::= Create (List Payload) | Supersede (Finset StandingId) (List Payload)
                 | SetStatus (Finset StandingId) (Active | Suspended)
NormEffect     ::= Standing StandingEffect | Transfer StandingId PrincipalId
targets, fresh  : StandingEffect -> Finset StandingId
delta           : (alpha : StandingEffect) -> (targets alpha -> StandingState)
                                           -> (targets alpha -> StandingState) x (fresh alpha -> StandingState)
applyEffect     : NormativeView -> NormEffect -> NormativeView
applyEffect V (Transfer _ _) = V
tag, rootTag    : Time x Nat -> StandingId / AnsRootId        -- F1-F3

SchemaCode : Type   [[.]]_S : SchemaCode -> (Match x PreState -> NormEffect)          -- S1-S6
DemandCode : Type   [[.]]_D : DemandCode -> (AnsRoot x Multiset Response x CitedDigest -> Prop)  -- D1-D2
steps      : Derivation -> Finset StandingId

Settlement = (id, refs : Finset SettleId, tau)
ReasonOcc  = (id, s_V : Finset V, s_L : Finset SettleId, t : V, tau)
NormEvent  = (id, cert : (Derivation x StandingId x Match), author : PrincipalId, tau)
Response   = (id, roots : Finset AnsRootId, cited : Finset NormEventId, tau)
AnsRoot    = (id, creditor, debtor, subject, demand : DemandCode, origin, tau)

S_t        = (L_t, R_t, N_t)
Seed       = (Std_0 : NormativeView, Roots_0 : Finset AnsRoot)
SystemStep ::= Settle Settlement | Reason ReasonOcc | Norm NormEvent | Respond Response

PreState_{<tau}    := (L_{<tau}, R_{<tau}, N_{<tau}, tau)
effect a           := [[payloadSchema (Std_{<tau a} (schemaRef a))]]_S (wit a, PreState_{<tau a})
basis a            := ReasonLeaves (D_a)
Std_t              := fold applyEffect Std_0 (map effect NormEvents_{<=t})
Roots_t            := Roots_0 ∪ union MINT a
B^_t               := { c : Std_t x = (Active,_,PCmt (StanceBearing, c)) }
O_t                := { cl : Std_t x = (Active,_,PForce (_,_,cl)) }
Digest a           := (tau a, author a, effect a, { id q | Disposes a q })
StandingChanges a x := standing(Std_{<=tau a}, x) != standing(Std_{<tau a}, x)
Closed_t q         := [[demand q]]_D (q, Responses_t q, CitedDigest (Responses_t q))
Live_t q           := q in Roots_t and not Closed_t q
Due_t q            := Live_t q and exists a in NormEvents_t. Disposes a q
CurrentEpisode_t q := Live_t q and not Due_t q
HasCustody_t P x   := exists! q. CurrentEpisode_t q and subject q = x and debtor q = P
succ_t q           := { q' in MINT a | Disposes a q, tau a <= t }
Desc*_t q          := least set containing q closed under succ_t
ContinuityOK_t q   := (Live_t q and not Due_t q) or (Closed_t q and forall q' in succ_t q. ContinuityOK_t q')
Good S             := GC S and AC S
```

**Derived lemma, outside the main theorem.** For a stage `Stage(A, s)`:

```text
I_s^{A_s}   = { q in Roots_s : creditor q = Stage(A, s) }
New_t^{A_s} = { q in Roots_t \ Roots_s : creditor q = Stage(A, s) }
```

**[THM] Source Closure.** `New_t^{A_s} = {}` for every `t >= s`. Minting stamps
`creditor = Stage(author a, tau a)`, and any root arriving after `s` has
`tau(a) > s`, so its creditor differs in the time component. This is what makes
the uniform creditor rule of §17 safe: inheriting a creditor on transfer would
create a root at `t > s` bearing `Stage(A, s)`, and the closure would fail.

---

## 34. Mechanization order

Each item depends only on earlier ones.

1. `Time`, ids, `tau` injectivity; the three ledgers and their append operations.
2. `Payload`, `StandingState`, `NormativeView`; `StandingEffect`, `NormEffect`,
   `targets`, `targetsN`.
3. `tag`, `rootTag`, F1-F3; `fresh`, `fresh_i`; the Fresh Allocation theorem
   (§13), which everything about EP consumes.
4. `delta`, `applyEffect`; Standing Locality and Transfer Neutrality (§12.3).
5. `SchemaCode`, `[[.]]_S`, S1-S6; `PreState`.
6. `WFSeed`, Z1-Z6.
7. `Derivation`, `steps`, `basis`; `WF` in the order G1-G6, and `effect` as the
   partial function defined at G4. Effect Determinacy.
8. `AnsRoot`, `MINT`, `Roots_t`; `Std_t` as the fold. `StandingChanges`,
   TargetCoverage.
9. `DemandCode`, `[[.]]_D`, D1-D2; `Digest`, Digest Stability, `CitedDigest`
   monotonicity.
10. `Closed`/`Live`/`Due`, trichotomy; `Disposes`, disposition uniqueness;
    "closure needs a disposer" (§10).
11. Fate Monotonicity; closure passes through `Due`.
12. `CurrentEpisode`, EP (§20) — base from Z3, Z3', Z6, D2; step by cases.
13. `HasCustody`, Custody Locality.
14. `succ`, `Desc*`, well-foundedness, the key lemma; `ContinuityOK`;
    Due-Witness.
15. `GC`, `AC`, `Good`; L1-L4; the main theorem.
16. Source Closure; FAIR and §30, kept separate.

---

## 35. Vertical-slice interface

The pipeline the core is frozen for:

```text
Gamma -> L -> R -> N -> O -> K -> trader -> Logical Inductor
```

What the core supplies, and nothing more:

| stage | supplied by |
|---|---|
| `Gamma -> L` | `Settle` steps; the settlement ledger is the only thing they write |
| `L -> R` | `Reason` steps; `s_L(e) subset ids(L_t)` is the only coupling |
| `R -> N` | `Norm` steps; `basis(a) = ReasonLeaves(D_a)` cites `R`, and `effect(a)` is certified by G1-G6 |
| accounting | `Respond` steps account for dispositions and produce none: no `Respond` step changes `Std`, `Roots` or any `Disposes` fact |
| `N -> O` | `O_t = { compiledClause p : Std_t x = (Active, _, PForce p) }`, a projection of the fold |
| `O -> K -> trader -> LI` | read-only consumers of `O_t`; nothing downstream is RI state, and no downstream object appears in `S_t` |

`PForce` standing is answerable like any other object: it carries a custody
episode, may be superseded, and its replacement is an ordinary `Supersede`.
Compilation `N -> O -> K` is not solved here; what is established is that the
step type imposes no obstruction to it.
