# The settlement ledger as a source for the LI epistemic substrate

`ARCHITECTURE.md` is this round's canonical account of the objects; this
document assumes it.

Status: **audit; unregistered.** Names provisional.

The hypothesis under audit:

> The settlement ledger is the provenance-bearing interactive generalization of
> the epistemic role played by the deductive process, while `PC(...)` /
> compatible completions provide the world semantics.

**Verdict: correct after a local reformulation.** The reformulation is that
`Sigma_n` is not `D_n` *composed alongside* a deductive process — it *is* the
deductive process. The pinned formalization has one slot, both channels feed it,
and no new world semantics is needed.

---

## 1. What `DeductiveProcess` actually requires

From `Framework/Criterion.lean` at the pinned commit:

```text
structure DeductiveProcess where
  D    : N -> Finset Sentence
  mono : forall n, D n subset D (n+1)

PCWorld.ConsistentWith v D := forall phi in D, v.Holds phi
```

Two fields. There is **no** requirement that `D n` be deductively closed, be a
theory, consist of theorems of anything, be logically consistent, or arise from
a proof search. Computability is a separate predicate
(`ComputableDeductiveProcess`), and the criterion's own definition takes it as a
side condition rather than building it into the type.

So the object is already a *finite monotone stream of sentences with a program
that emits it*, and its name understates it. Any source meeting those conditions
is a legal source, and

```text
Sigma_n = D_n union Sem_L(L_n)
W_n     = PC(Sigma_n)
```

is a `DeductiveProcess` whenever `Sem_L(L_n)` is finite and monotone. The
equivalence the addendum proposes,

```text
PC(Sigma_n) = PC(D_n) ∩ Compat(L_n),
```

is immediate rather than a design choice: `ConsistentWith` is a universal
quantifier over membership, so it distributes over the union. That is the local
reformulation — the two presentations are the same object, and the union form is
the one the type accepts.

## 2. Ledger versus theory — the distinction holds

`L_n` is not identified with a theory. The ledger is the append-only
provenance-bearing history; `Sem_L(L_n)` is the induced sentence set; and the two
are separated by a function.

Two settlement histories with different entries, different provenance and
different order induce the same `Sigma_n` whenever their per-entry denotations
union to the same set — the model's `Stage.of` deduplicates on the sentence,
keeping the first source, which is what `Finset Sentence` already means on the
other side. History lives in `L_n`; current epistemic restriction lives in
`PC(Sigma_n)`. The `source` field on a stage entry is provenance and has no
semantic role: `ConsistentWith` reads the sentence and nothing else.

## 3. Totality of `sem_L` — right, in the weak form

The addendum asks whether every genuine settlement should carry a rigid LI-facing
denotation. The type forces the total form and the strength claim should be
weakened:

```text
sem_L : SettleId -> Finset Sentence          -- total
```

Totality is free, because "no exact semantics yet" is `{}`, which constrains no
world. So the defensible principle is **not** "every genuine settlement has exact
world-compatibility semantics" — that is too strong and would make admission to
the ledger wait on interpretation. It is:

> Every settlement has a rigid total denotation, possibly empty; a reason or
> normative expression need not have one at all.

That asymmetry with `V` is principled, and the reason is the type rather than
taste. A sentence set is what the world semantics consumes; `V`'s objects are
consumed by nothing that quantifies over worlds. `V` reaches `L` through rigid
quotation and selective exposure; a settlement reaches the substrate through a
total function into `Finset Sentence`, whose empty value is the non-exposure
state. The value waist's `NonExposure` and the settlement layer's empty
denotation are the same device at two places, which is evidence the shape is
right rather than a coincidence.

## 4. Raw outcome versus formal settlement — the layer is needed

`RawOutcome -> SettlementReading -> L_n` is not decoration. Two things force it.

**Computability.** `IsLogicalInductor` needs one program emitting `Sigma_n`. A
natural-language observation dropped into a world-constraining ledger is not that,
and `E3` cannot be discharged for it. The certified reading is where a total
computable function can exist.

**Ambiguity must not eliminate worlds.** An observation with no exact account of
what was settled gets `{}`, enters with its provenance and its `of_outcome`
pointer, and removes no world. `test_settlement.py` checks that the world count
is unchanged. `settlement != assessment != reason` survives: `sem_L` takes a
settlement id and nothing else, so there is no parameter through which normative
interpretation could enter.

## 5. Failure cases

**Two settlements whose contents conflict.** `Sigma_n` becomes unsatisfiable.
Nothing repairs it and neither entry is dropped; `conflicting_sources` returns
minimal attributable source sets.

**Settlement against `D_n`.** Same, and the attribution names both channels.
Neither wins. Threshold coherence is deductive, so a reading affirming
`X > 2/3` while denying `X > 1/3` is exactly this case.

**And the reason it must be checked.** The pinned
`isLogicalInductor_of_stage_unsatisfiable` proves the logical-induction criterion
holds over a process with an unsatisfiable stage, because every quantifier in the
criterion ranges over consistent worlds. So a contradictory ledger does **not**
break the guarantees — it empties them. Admissibility becomes vacuously true and
the live-world deficit vacuously zero, and an architecture reading those numbers
without checking satisfiability would read maximal safety off a contradiction.
The pipeline reports `D-stage-unsatisfiable` before any obligation is evaluated.

**Conservative extension after old settlements.** New atoms, new stage
sentences about them and a new settlement mentioning only them leave the day's
coordinates, rows, `K^D`, `K` and live-world deficit identical.

**Rigidity of old denotations.** `SettlementSemantics.admit` refuses a second
reading for an id. An old settlement's denotation is unchanged by later language
growth.

## 6. Monotonicity is what makes settlement irreversible

`DeductiveProcess.mono` is a field of the type. A settlement that could be
retracted would shrink `Sigma`, break `mono`, and leave no object of that type to
hand a trader.

So Reflective Integrity's rule that the settlement ledger is append-only and
"settlements do not defease" is not merely prudent record-keeping: **it is the
condition under which the ledger can feed the LI substrate at all.** If something
in the environment can turn out false, it was an observation and not a
settlement, and the fallible layer upstream of formal settlement is `RawOutcome`,
which the architecture already has.

## 7. One substrate, not several

Value-generated LUVs, ordinary proposition prices and environmental settlements
inhabit one semantic substrate, and the check is that they all bottom out in the
same two objects. A LUV is a family of `Sentence`; a threshold's price is an
ordinary sentence price; `sem_L` returns `Finset Sentence`; and a world is a
`PCWorld` valuing all of them by `Holds`. There is no second notion of world
anywhere in the slice. The `values` field of a `CertifiedLUV` is a world-value
presentation in the pinned `ExactTheoryPresentation` sense, and its content is
recoverable as stage sentences by `valued_at` — which is how the toy's settlement
pins a value.

## 8. The order in the toy

```text
raw outcome -> certified reading -> Settle step -> Sigma_{n+1} -> W shrinks
            -> P_n and E_n(X) move -> Reason step citing the settlement
            -> Norm step whose derivation has that reason among its leaves
```

This is the order the record forces rather than one chosen: a settlement is
appended before a reason may cite it (`s_L(e) subset ids(L_t)`), and a reason
occurs before the event whose derivation has it among its leaves
(`ReasonLeaves(D_a) subset ids(R_{<tau(a)})`). The epistemic effect and the
normative effect are separate steps, and between them the record is in a state
where the world has moved and normative standing has not.

## 9. What this audit does not establish

- `E3` is stated and not discharged. No `Primrec` or `Nat.Partrec.Code`
  statement is made about any `Sigma` here.
- The claim that totality is "free" is an argument from the type, not a survey of
  what settlements can be. A settlement whose natural content is not a finite
  sentence set is representable only as `{}` plus a note, and whether that is
  adequate for real normative practice is untested.
- The deduplication argument in §2 shows two histories *can* induce one
  `Sigma_n`; no characterization of when they do is offered.
- Nothing here says whether `D_n` and `Sem_L(L_n)` should stay distinguishable
  once unioned. The model keeps a `source` field, and no theorem consumes it.
