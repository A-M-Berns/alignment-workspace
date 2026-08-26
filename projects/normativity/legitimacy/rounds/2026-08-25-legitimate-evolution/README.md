# Grounded Replay

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

DUE-REALIZATION-GAP — the abstract package stabilizes and Reflective Integrity still cannot realize it. Three repairs made it stable. The carry law was too strong: requiring successors to be freshly opened refused ordinary consolidation into a claim already outstanding, and the correct law is that the successor set is non-empty and outstanding after the step, which also subsumes the strict-pre-state protection. Due is an activation generator over the whole represented state, not a predicate on a reason: a persistent predicate makes answering an answerable claim illegitimate, since the reasons stay represented and keep reactivating it, and minting on reason arrival cannot see material that only a later normative state makes owed. And splitting incurred from outstanding — the entitlement side's admitted-versus-live — lets the theorem quantify over every claim ever taken on, so a claim incurred and resolved by one event is still something the theorem speaks about. The central finding is a layer correction to the previous pass: D1 is not a premise of the answerability theorem. The induction never consults it, and a process with impeccable entitlement, no removals at all, and a represented reason its own semantics activates satisfies A1, the theorem and no-silent-loss while never taking the claim on. D1 does not make the proof work, it makes the conclusion quantify over the right set, so it is a conformance condition at the realization boundary. RI has three of the four pieces already — roots against live is the incurred/outstanding split, Respond settles without a NormEvent, and continuity_ok recurses over successors with the right leaf condition — and lacks only an activation step; and the previous pass's recommended seam, a minting trigger keyed on reason occurrences, is refuted by the old-reason-becomes-newly-due case.

Round 5's `PROPER-EXERCISE-SEMANTIC-ONLY` stands unchanged, and this round did
not reopen it. Grounded Replay was frozen for this pass: `src/replay.py` is
untouched, imports neither the Proper Exercise analysis nor the answerability
replay, and has no capability or obligation notion in either of its records.

**The question this pass was dispatched to settle** was whether the Due bridge
and the resolution law can be made small and correct enough to freeze. They can,
and the freezing is blocked by the realization rather than by the mathematics.

The thing worth carrying forward is the layer correction. A morally important
sentence — *what the process recognizes as owed must be taken on* — was shipped
last pass as a premise of an induction that never uses it. Stating it in the
right place changes what a realization has to supply: a structural premise is
discharged by construction, and a conformance condition has to be checked against
an implementation and can fail there while every theorem still holds.

The other three repairs are ordinary. The carry law was refusing legitimate
consolidation. `Due` as a predicate on a reason either reopens resolved claims
forever or misses material that only a later normative state makes owed. And the
theorem was quantifying over a set that forgets.

`ANSWERABILITY.md` opens with the whole package on one page.

## The statement

```text
L_0     = G
L_{t+1} = (L_t \ dispose(e_t)) union issue_t(e_t)   if Valid(L_t, e_t)
          L_t                                        otherwise
```

```text
S1   grounds(e_t) subset { o in L_t : Auth(o) }
S2   apply_t(L_t,e_t) != L_t  ->  grounds(e_t) != {}
```

> Every occurrence the replay has ever admitted has a finite grounding tree:
> leaves in `G`, internal nodes accepted edits, children the grounds that edit
> invoked, and positions strictly descending.

with three corollaries — no self-ratification, no laundering, persistence until
an accepted edit disposes it. `LEGITIMATE_EVOLUTION.md` opens with the whole
statement on one page.

## What the prosecutions found

**The grounding theorem was false.** An edit with no grounds satisfies prior
grounding vacuously and issues an occurrence whose only tree is a leaf outside
the base. `S2` is the repair, and the right form is *state-changing* rather than
*any* edit: a no-op needs no authority, and grounding and persistence consume the
two halves.

**Historical time was being used as identity.** Two edits at one time issued the
same occurrence. The trace is a list; position is identity and order at once;
freshness stops being a premise.

**Soundness at a checker's own state is worth nothing.** A checker that misses a
valid revocation keeps an authority the semantics removed and then admits a stale
use of it — and the previous pass's soundness notion reports that clean. The
exact condition is agreement along the trace, it is weaker than global equality,
and **both** consumers need it. The previous pass's asymmetry between them is
withdrawn.

**A grounding tree cannot certify currentness.** A tree is built from grounds and
disposals are not grounds. So deference, which needs current authority, does not
get a finite certificate — it needs a replay, a commitment scheme nobody has
built, or an attestation.

**Content invariance was vacuous and is false.** The check replayed the unchanged
process, and permission reads content once a live policy can ban a scope.

## What got smaller

```text
before                          now
six hypotheses H1-H6            two premises S1, S2
Valid primitive + 3 assumptions Valid defined
ProvOK refusing influences      ProvView describing + Permit deciding
Occ = (at, index, sort)         Occ = (pos, slot)
declared/effect split + H5      the effect is in the edit; H5 is extraction
Auth/Norm a partition           Auth a predicate; Norm lives in the realizations
G1..G6                          one theorem, three corollaries
```

## Contents

- `ANSWERABILITY.md` — the minimal package, the second replay, and H-A.
- `LEGITIMATE_EVOLUTION.md` — the minimal statement, then the layers.
- `PROPER_EXERCISE.md` — the fourteen separations, and why there is no
  no-escalation theorem.
- `CROSS_PROCESS_INTERFACE.md` — origin, historical and current, and what each costs.
- `CONSUMER_TEST.md` — deference, and which of the three it needs.
- `TRADERIZATION_CONSUMER.md` — enforcement, and the four repeal cases.
- `COUNTERMODELS.md` — every premise prosecuted; withdrawals are §§1-5 and
  §§12-18.
- `THEOREM_MAP.md` — every claim graded, withdrawals first.
- `src/` — `replay.py` (the kernel), `office.py` (the semantics and a
  constitution model, importing no record architecture), `ri_frame.py`
  (extraction from a record), `exercise.py` (capability and reach),
  `answer.py` (incurred and outstanding claims, Due and Resolve), `cases.py`
  (records the Carroll round did not have).
- `tests/` — 126 cases. `python3 tests/run.py`.

## What this does not establish

No Lean and no registered claim.

Provenance completeness is an assumption, not a condition. It is not "assume the
relevant influences are visible", not "refuse every influence", and not derivable
from a record whose own episodes cover by construction.

`Permit` is opaque. A constitution with a permissive one satisfies every theorem
here.

Reflective Integrity has no jurisdiction on an authority, so the permit clause is
nearly vacuous on a record — and an external-rule discipline cannot substitute,
because a `NormEvent` has no slot for citing a governing protocol. That is a gap
the abstraction exposed and this pass deliberately did not repair.

No structure on permission was needed for the fourteen separations, and the round
does not claim none could be useful for something else. What it claims is that the
natural candidate — capability monotonicity under delegation — is refuted by
constitutional widening.

Answerability says nothing about progress. An obligation may stay open forever
and both theorems are satisfied; `unobservant()` never notices anything and is
legitimate; `high_regret()` repeats the same bad choice three times and is
legitimate. Coverage — that some situation *ought* to have become due — remains
where round 3 left it, outside.

The realization gap recorded in `ANSWERABILITY.md` §6 has not been checked
against the Reflective Integrity code. It is stated as a question for the
maintainer, not as a result.
