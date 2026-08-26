# Grounded Replay

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

LEGITIMATE-EVOLUTION-NEEDS-DUE-BRIDGE — three things in the shipped package were wrong and are repaired here, and the one that remains is the seam the package is named for. Answerability Continuity's conclusion was false on every process that resolves an obligation after transferring it: transfer-then-discharge, split-then-discharge-both and merge-then-discharge all have clean premises and failed it, because the statement tracked a root's own fate where succession replaces it with others. The corrected conclusion asks for a finite resolution derivation with a non-empty frontier of open-or-discharged leaves, a tree unfolded from a DAG. A2 was doing no work — a hand-built cycle violating freshness maximally still satisfies the theorem, since termination comes from the interval and not from occurrence identity — and is demoted to representation hygiene. And one acceptance bit could not gate both channels: an unauthorized act whose occurrence is itself owed an answer could open nothing, so the gate is now asymmetric, openings ungated and removals gated, which keeps the corollary that an unentitled act discharges nothing and adds its converse. The remaining gap is Due: a process may recognize a represented reason as owed and never enter it, which D1 now forbids abstractly, and which Reflective Integrity cannot realize — roots() mints from NormEvents only, checked against the code, and RI's own due() is a different predicate.

Round 5's `PROPER-EXERCISE-SEMANTIC-ONLY` stands unchanged, and this round did
not reopen it. Grounded Replay was frozen for this pass: `src/replay.py` is
untouched, imports neither the Proper Exercise analysis nor the answerability
replay, and has no capability or obligation notion in either of its records.

**The question this pass was dispatched to settle** was whether the pair is
actually the smallest correct package, or whether the answerability side is still
one semantic seam too weak. It was too weak, and in three places at once.

Two of the three were outright errors rather than gaps. The continuity conclusion
was false — not under-proved, false, on a family of ordinary processes. The second
premise was inert. Both were found by building the instance rather than by
inspecting the statement, which is the same method that found the previous three
defects in this object.

The third is the one the dispatch flagged and is a design error rather than a
mistake: sharing one acceptance bit between the two folds made it impossible to
represent a process that becomes answerable for an act it refused. The corollary
the shared gate was introduced to secure survives the repair; what it gains is the
converse.

What remains open is `Due`. The package can now say that a recognized obligation
must be entered, and Reflective Integrity has no way to realize that: it mints
answerability roots from normative effects only. The seam is one function, not a
new event kind, and it is not built.

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
  §§12-15.
- `THEOREM_MAP.md` — every claim graded, withdrawals first.
- `src/` — `replay.py` (the kernel), `office.py` (the semantics and a
  constitution model, importing no record architecture), `ri_frame.py` (extraction from a
  record), `exercise.py` (capability and reach, an analysis over frames),
  `answer.py` (the second replay, over obligations), `cases.py` (records the
  Carroll round did not have).
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
