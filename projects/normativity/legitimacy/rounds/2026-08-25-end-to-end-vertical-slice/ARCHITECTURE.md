# The forward normative reasoner

Status: **specification; unregistered.** Names provisional under `AGENTS.md` §6.
Nothing here is Lean-checked. Every structural claim is exercised by
`tests/test_architecture.py`; every claim about the pinned Logical Induction
dependency was read at `c0d885bfb2f84054ada18c65acec672e04d6d380`.

This is the canonical account of what the round built. `VERTICAL_SLICE.md` is
the clause-by-clause specification, `FINDINGS.md` the research report; both
defer to this document for what the objects *are*.

---

## 1. The four kinds of thing

Every named object is exactly one of these, and most of the accumulated prose in
this line reads as though there were more.

| kind | mutates? | examples |
|---|---|---|
| **parameters** — fixed before the trajectory, meta-stable, conservative extension only | never | `V`'s grammar, `[[.]]_S`, `[[.]]_D`, `sem_L`, `valueSem`, `tag`, `rootTag`, `Time` |
| **historical occurrences** — append-only, identity-bearing, never rewritten | grows | `Settlement`, `ReasonOcc`, `NormEvent`, `Response` |
| **bounded resource** — the only thing that shrinks | shrinks | `OutflowAccount` |
| **derived views** — recomputed by replay; stored nowhere | n/a | `Std_t`, `B̂_t`, `O_t`, `Values_t`, `Roots_t`, `Σ_t`, `W_t`, `K^D`, `K^N`, `K`, fates, custody |

The compression this buys:

```text
MachineState_t  =  History_t  ×  PriceHistory_{<t}  ×  Account_t
```

and nothing else is state. `History_t = (L_t, R_t, N_t)` is Reflective
Integrity's three append-only ledgers over a seed parameter.

**Why the two registries are not state.** The reference model carries a
`ValueRegistry` and a `SettlementSemantics`, both write-once. Conceptually
neither is a store: `sem_L : SettleId → Finset Sentence` and
`valueSem : ValueSpecCode × QueryCode ⇀ CertifiedLUV` are *total rigid partial
functions over their whole code spaces*, in exactly the shape `[[.]]_S` and
`[[.]]_D` already have, with `∅` and `NonExposure` as the default values.
`Sem_L(L_n)` grows because `L` grows, not because `sem_L` changes. The
write-once gate is an implementation device enforcing that rigidity, and
refusing a second reading for an id is what makes it visible.

---

## 2. The reason substrate is a directed multihypergraph

```text
ReasonOcc e = (id, s_V : Finset V, s_L : Finset SettleId, target : V, tau)
V ::= Atom p | Neg V | App(σ, c, n) | Inst(e, σ)
```

Each occurrence is a directed hyperedge over the vertex universe
`U = V ⊔ SettleId`:

```text
e :  s_V(e) ⊔ s_L(e)  ⟶  target(e)
```

with a finite set of tails and a single head. Distinct occurrences may carry the
same `(s_V, s_L, target)`, so the structure is a **multi**hypergraph: the edge
is the occurrence, not the shape.

Four things it deliberately does **not** represent.

**Sources are content, not occurrences.** `s_V : Finset V` holds reason
*expressions*; an occurrence never cites another occurrence. So the graph is a
support structure over content, and occurrence-level provenance is a separate
object — `Derivation`, which cites `ReasonOcc` *ids* as leaves. Two occurrences
with the same content are distinguishable exactly there.

**Enablement does not propagate.**

```text
Enabled_{B,L}(e)  ⟺  s_V(e) ⊆ B  ∧  s_L(e) ⊆ L
```

reads two vertex sets — the stance `B̂_t` and the ledger `L_t` — and never
another edge. There is no fixpoint, no label to maintain, no update procedure.
This is the reason-representation round's result, visible in the type: the
substrate is a family of stateless queries, and everything a truth-maintenance
system *does* is a stance policy plus caching.

**Having a reason is not taking a stance.** `B̂_t` is a fold over *standing* —
the contents of active `PCmt(StanceBearing, ·)` objects — not a closure of the
graph. An edge whose tails are all in `B̂_t` does not thereby put its head there.
Adopting a conclusion is a normative act with an event behind it.

**Undercutting needs no attack primitive.** A reason against applying `σ` to
case `c` at stage `n` is an ordinary occurrence with target
`Neg(App(σ, c, n))`. The involutive negation in `V` is what makes this
statable, which is why the reason-representation round found a contradiction
floor to be forced.

So:

```text
reason graph        vertices V ⊔ SettleId ; edges ReasonOcc ; identity-bearing
derivation          selected occurrence-level provenance through that graph,
                    plus licensed inference steps
```

---

## 3. Schemas are rigid; standing toward them is revisable

The reflective structure, and the round's claim is that it needs **no new
mechanism**.

```text
PAuth : SchemaCode → Payload            standing carrying a schema
steps : Derivation → Finset StandingId  inference-step licences
G3    each step names an active PAuth at the strict pre-state
G4    schemaRef(a) names an active PAuth at the strict pre-state
      effect(a) := [[σ]]_S (wit a, PreState_{<τ(a)})
```

`SchemaCode` and `[[.]]_S` are meta-stable: a schema's meaning never changes.
What changes is **which standing is active carrying which code**, and that moves
by ordinary supersession:

```text
PAuth(σ₀)  ⇝  PAuth(σ₁)          Supersede({x}, [PAuth σ₁])
```

The old standing is `Terminated`, keeps its payload, and keeps its lineage in
the successor's `pred`. An old derivation naming it stays interpretable, because
`WF(a)` was decided once at `τ(a)` against a prefix that never changes.

The loop closes:

```text
active PAuth standing
      ↓  licenses inference steps, and supplies the schema interpreted as the effect
reason multihypergraph  →  Derivation
      ↓
   NormEvent
      ↓  effect(a)
may supersede that same PAuth standing
```

and the last arrow is real rather than notional: a schema can license the very
event that retires its own standing, and the record stays `Good`
(`test_architecture.py`). What is excluded is the other direction — an event
licensed by standing it *creates* — and that is excluded by the allocator, since
fresh ids are disjoint from the strict pre-state's domain, not by a side
condition.

---

## 4. The settlement ledger and the LI epistemic projection

The seam, stated exactly.

```text
L_n                     provenance-bearing append-only settlement history
sem_L : SettleId → Finset Sentence          rigid, total, fixed at admission
Sem_L(L_n) = ⋃_{ℓ ∈ L_n} sem_L(id ℓ)
Σ_n        = D_n ∪ Sem_L(L_n)
W_n        = PC(Σ_n) = { v : ∀ φ ∈ Σ_n, v.Holds φ }
```

**`Σ_n` is not a second object beside the deductive process — it is one.** The
pinned `structure DeductiveProcess` has exactly two fields, `D : ℕ → Finset
Sentence` and `mono`, with no requirement of closure, consistency, or
provenance from a proof search. Any finite monotone sentence stream is a legal
one. `PC` distributes over the union because `ConsistentWith` is a universal
quantifier over membership, so `PC(Σ_n) = PC(D_n) ∩ Compat(L_n)` is a
restatement rather than a design choice.

Three consequences.

**Monotonicity is a theorem, not an assumption**, given that `L` is append-only
and `sem_L` is per-entry and rigid. Conversely a settlement that could be
retracted would shrink `Σ` and break `mono`, leaving no object of the type to
hand a trader. **Irreversible settlement is forced by the type.**

**Provenance is forgotten exactly at `PC`.** The ledger remembers what settled
and on whose authority; `sem_L` projects that into `Sentence`; `PC(Σ_n)` retains
only the induced restriction. Two histories with different entries, outcomes,
notes and orderings can therefore induce the same `Σ_n`, the same worlds and the
same deficit while staying distinguishable upstream — checked in
`test_settlement.py`.

**The layers below settlement stay separate.**

```text
RawOutcome  ≠  Settlement  ≠  sem_L(Settlement)  ≠  ReasonOcc
```

A raw outcome is what an ambiguous observation is; it never reaches the ledger.
A settlement with `sem_L(ℓ) = ∅` is admitted with its provenance and eliminates
no world — the settlement-side counterpart of `NonExposure`, and the reason
totality of `sem_L` is free rather than strong. `sem_L` takes a settlement id
and nothing else, so no reason, standing or event is in scope and normative
interpretation cannot enter the world semantics.

**The contradiction guard is load-bearing.** An unsatisfiable `Σ_n` does not
break the guarantees; `isLogicalInductor_of_stage_unsatisfiable` makes the
criterion hold vacuously, so admissibility passes vacuously and the deficit is
vacuously zero. The pipeline reports `D-stage-unsatisfiable` and emits no
obligations, *before* anything downstream could read those numbers as safety.

**On the type of the reading.** The round keeps Reflective Integrity's thin
`Settlement` and puts the reading beside it, keyed by id. `SettlementReading`
is an application-level object carrying `of_outcome`, the sentences and a note;
RI forgets it down to an id in `L`. The alternative — a `content` field on
`Settlement` — would change a record type in the frozen core's §33 signature to
buy the same thing, and is refused on that ground rather than on taste.

---

## 5. Standing and answerability are derived

```text
Std_t = fold Std_0 over NormEvents_{≤t} in τ-order, applying applyEffect
B̂_t   = { c : Std_t x = (Active, _, PCmt(StanceBearing, c)) }
O_t   = { (x, J) : Std_t x = (Active, _, PForce(_, _, J)) }
Val_t = { (x, v) : Std_t x = (Active, _, PValue v) }
Roots_t, Live/Due/Closed, CurrentEpisode, HasCustody, succ_t   — all folds
```

Custody is not stored; it is the unique current episode with a given subject and
debtor, which is what makes Custody Locality a theorem rather than a convention.

**Three graphs, three questions, no shared vertices.**

| graph | vertices | edges | answers |
|---|---|---|---|
| reason multihypergraph | `V ⊔ SettleId` | `ReasonOcc` | what supports what, in content |
| standing lineage | `StandingId` | `pred` under `Supersede` | what replaced what |
| answerability succession | `AnsRootId` | `succ_t` via `MINT`/`Disposes` | who owes what next |

They are not one graph. `test_architecture.py` checks the vertex universes are
disjoint.

---

## 6. The three waists

```text
valueSem   : ValueSpecCode × QueryCode  →  CertifiedLUV + NonExposure

CognitiveQuantity ::= Prob(Sentence) | Expect(CertifiedLUV)

Affine(A)  = finite rational affine expressions over A
Injunction = finite nonempty family of inequalities in Affine(CognitiveQuantity)

κ_n : O_n  →  (coords : Sentence*, rows : rational rows over prices)
```

**`Expect` is not a new security.** `[[Expect(X)]]_n = E_n(X)` is
`X.expectAffine (n+1)` priced on day `n`, and `expectAffine_price` in the pinned
dependency is already the statement that these agree. `AffineCombination` —
`const + Σ eᵢφᵢ` over sentences — already subsumes both `Prob` and the expansion
of `Expect`, and `LUVCombination` with `meshAffine` is already the affine-over-
LUVs type. The cognitive waist *names* a language that exists; it does not build
a bridge.

**`PInjunction` is not a new payload.** It is `PForce`, which Reflective
Integrity already has, with `Clause` already opaque and `O_t` already its
projection. `PForce`'s two reference fields are inert: `κ` reads `clause` and
nothing else.

**`PValue` is a new payload constructor and costs nothing.** `delta`'s three
clauses write a payload into a fresh standing state without inspecting it, so no
clause of `applyEffect` changes and no existing term changes. Meta-Stability
licenses exactly this.

What the running code showed must be kept: duplicate sentence coordinates merge
(`nodup`); standing identity survives the projection; several value
specifications need no aggregation rule, because a quantity is named after the
frozen specification that exposed it; `NonExposure` is non-destructive; and a
frozen high-level payload does **not** mean a frozen day-level row system.

---

## 7. Two independent channels, meeting once

```text
epistemic:   L_n --sem_L--> Sentence*   ⊎   D_n   ⟶   Σ_n   ⟶   PC(Σ_n)   ⟶   K^D_n
normative:   N_n ⟶ Std_n ⟶ O_n ⟶ κ_n ⟶ rows ⟶ K^N_n

               K_n  =  K^D_n ∩ K^N_n
```

`K^D_n` is a function of `Σ_n` and the fragment and reads no injunction; the
compiled rows are a function of `O_n` and the day and read no world. They meet
at an intersection and nowhere else.

The composition is decided in barycentric coordinates: `K^D` arrives as a vertex
list, turning one into rows is facet enumeration the repository declines to
perform, and a point of the intersection is `Σ λ_v v` with `λ` in an explicit
polytope. Nonemptiness, a Farkas certificate and a generating vertex list for
`K_n` all come from that one weight system.

**Conflict is detected and certified, never resolved.** Four states — malformed
payload, self-inconsistent injunction, empty joint demand, region incompatible
with deduction — plus the unsatisfiable stage. Fourier–Motzkin combines
constraints by positive multiples, so multipliers compose linearly and a derived
contradiction arrives carrying the Farkas certificate whose support names the
responsible standing and inequality index. No separate attribution mechanism is
needed.

---

## 8. The charged traderization boundary

**The dichotomy.** On the non-blocking domain — a nonempty live-world set and a
well-formed, jointly satisfiable demand:

```text
hadm  ⟺  K^D_n ⊆ K^N_n  ⟺  K_n = K^D_n
```

Forward, because `K^N` is convex and contains the vertices of `K^D`; backward,
because `K^D` is the hull of the live patterns. So the unconditional
traderization theorem's hypothesis holds exactly for injunctions that change
nothing about the prices.

The reading is **not** that traderization fails for normativity. It is that the
unconditional branch is the deductively inert, zero-liability calibration branch
— which is what the deduction special case already says about deduction — and
that genuinely region-changing normativity uses charged enforcement.

**The charged branch, and the object it is stated about.**

```text
ForceRequest = (date, support, rows, live_worlds, ε_t, M_t, δ_t)
D_t          = max_{ω ∈ live} Σ_j d_{t,j}(ω)
q_t          = (ε_t + M_t) · D_t / δ_t
```

`LiveDeficitCertificate.binds` checks four identities — date, row presentation,
support, live worlds — so the theorem-facing object is **a presentation together
with an assessment, not a region**. Two requests enforcing the same prices are
different requests if their rows differ, and they are charged differently.

Three separated claims about what settlement buys:

1. **fixed presentation, support and day:** narrowing the live-world set cannot
   raise `D`, because `D` is a maximum. This is the only monotonicity available.
2. **across days:** `κ_n(J)` changes, the fragments change, and `D_n` **can
   rise**. The precision-`k` reading of a value is `⌈xk⌉/k`, which is not
   monotone in `k`; a frozen `Expect(X) ≤ 1/2` against a stage settling
   `X ≤ 1/2` gives `D_1 = 0` and `D_2 = 1/6`, and still rises when the day-2
   stage strictly grows. The two days' live-world sets are patterns over
   *different fragments*, so the cross-day premise is not well formed to begin
   with.
3. **the charge is not the deficit:** `q_t` carries `ε_t`, `M_t` and `δ_t`, so
   `D_t` falling does not make `q_t` fall.

**Presentation dependence.** `D_t` sums across rows before maximising over
worlds, so one demand stated twice costs twice and enforces the same prices. A
canonical form would have to choose a preferred row system for a region and
defend the choice; this round records the frontier rather than crossing it.

**Order, and what withholding means.** Certify, charge, debit, then construct the
position. Under `quarantine` an account that cannot fund `q_t` yields no force,
and then no price: the injunction keeps its normative standing and the market is
not moved. That is a withholding, not a violation.

---

## 9. Signature block

```text
-- parameters, meta-stable
Time : LinearOrder     StandingId, PrincipalId, NormEventId, AnsRootId, SettleId : Type
V   ::= Atom p | Neg V | App(σ,c,n) | Inst(e,σ)
Sentence, PCWorld, Holds, payout, ConsistentWith            -- pinned LI
[[.]]_S : SchemaCode → (Match × PreState ⇀ NormEffect)       -- S1–S6
[[.]]_D : DemandCode → (AnsRoot × Multiset Response × CitedDigest → Prop)  -- D1–D2
sem_L   : SettleId → Finset Sentence                         -- E1–E3
valueSem: ValueSpecCode × QueryCode → CertifiedLUV + NonExposure

-- historical occurrences, append-only
Settlement = (id, refs, τ)
ReasonOcc  = (id, s_V : Finset V, s_L : Finset SettleId, target : V, τ)
NormEvent  = (id, cert : (Derivation × StandingId × Match), author, τ)
Response   = (id, roots, cited, τ)
History_t  = (L_t, R_t, N_t)

-- payloads
Payload ::= PCmt (CommitmentRole × ObjTerm) | PAuth SchemaCode
          | PForce (StandingId × StandingId × Clause) | PProto ObjTerm
          | PValue ValueSpecCode                       -- the round's one addition

-- derived
Std_t, B̂_t, O_t, Val_t, Roots_t, Live/Due/Closed, succ_t
Σ_t = D_t ∪ Sem_L(L_t)          W_t = PC(Σ_t)          K^D_t = conv(W_t|coords)
K^N_t = ⋂_i [[κ_t(J_i)]]        K_t = K^D_t ∩ K^N_t

-- resource and certificates
ForceRequest, LiveDeficitCertificate, OutflowAccount, Farkas certificate

-- state
MachineState_t = History_t × PriceHistory_{<t} × Account_t
```

---

## 10. Sockets for the learning loop

The forward run computes these and hands them out; **none of them mutates `N`,
and none is a reason.**

```text
Farkas certificate        multipliers naming (standing, inequality index)
conflicting source sets   minimal subsets of Σ_n admitting no world
LiveDeficitCertificate    D_t, rowwise, and the four identities it binds
charge history            (q_t)_t and its partial sums
account state             remaining, lifetime ceiling, ledger
withheld-force events     a date on which standing stood and nothing moved
```

Preserved by the step types rather than by discipline:

```text
pressure ≠ inquiry ≠ service ≠ assessment ≠ reason ≠ NormEvent
```

**The loop is now built, and it consumed no new ontology.**
`INQUIRY_INTEGRATION.md` runs it end to end: a need derived from the real
charged result, an ordinary action through `Gamma`, a raw outcome read into the
existing settlement seam, a service certificate citing `SettleId`s, an
assessment checker over a proposed `ReasonOcc`, and an ordinary licensed
`NormEvent`. No `InquiryEvent`, `ServiceEvent`, `AssessmentEvent` or
`PressureEvent` was needed, and the record the loop produces is identical
to the canonical Stage B — same `tau`s, same minted ids.

Two things it added, both outside `MachineState_t`. The environment side gains
an `InteractionLog` that `Gamma` and a policy read and Reflective Integrity
never does. And `SettlementReading` gains one frozen field holding an
`InteractionProvenance` — `(receipt_id, receipt_index, action, outcome_id)` — the
**narrowest authenticated provenance bridge** that lets a service judge tell
"this was settled" from "this was settled by the designated procedure". It is
constructible only by resolving a real receipt against a real log and the
outcome being settled, so it is a procedural fact rather than a caller's
annotation. `sem_L` does not read it, no world reads
it, and `PC(Σ_n)` is still a function of the sentences alone — which is exactly
why service does **not** factor through `PC(Σ_n)`, demonstrated by two ledgers
with identical `Σ` and opposite service verdicts, both of them backed by a real
execution through a real `Gamma`.

`Std_t` changes only through `applyEffect` on a well-formed `Norm` step, so a
certificate cannot become force without an event.

Two constraints the forward run already imposes on any consumer. A signal
firing on a positive deficit fires on every contentful injunction, since by §8
that is all of them — so the signal is a property of the **charge history**, not
of a date. And `D_t` is not monotone across days, so a consumer watching for it
to fall is watching for something that need not happen even when inquiry works.

---

## 11. Open obligations

1. **The safety condition.** `Σ_t q_t < ∞` for a normative source anyone would
   call legitimate. Four synthetic trajectories are exhibited, two convergent
   and two not; no source is shown summable. `PRIORITIES.md` item 61.
   `ANSWERABILITY_SCOUT.md` gets partway: allowance on live answerability
   episodes, plus subadditivity of the deficit and two local succession laws,
   bounds `Σ_t c_t` by `Φ_0 + Σ η_t`. That reduces the question to what
   licenses a grant, which is the inquiry loop's.
2. **Presentation canonicalisation**, or a demonstration that no canonical row
   system for a region exists that is defensible.
3. **The dichotomy in Lean** — three lines, using only convexity. Item 62.
4. **Effectivity.** `Σ_n` as a `ComputableDeductiveProcess`, and
   `RationalConstraintSchedule.Computation` for the generated schedules. Both
   are declared, not proved. Item 63.
5. **`L_min(V)`.** Nothing here required an LI sentence meaning a reason; whether
   the stronger relation is needed is untested. Item 65.
6. **Nonconvex permissibility** has no representation anywhere in the execution
   layer — a limit of the architecture, in a different place from the waists.
