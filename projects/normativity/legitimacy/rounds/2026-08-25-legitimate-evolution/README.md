# Grounded Replay

Status: **specification, reference models and a prosecution record;
unregistered.** All names are provisional under `AGENTS.md` §6. Nothing here is
Lean-checked and no claim is registered.

## Verdict

PROPER-EXERCISE-SEMANTIC-ONLY — propriety resides in an opaque permission relation and no generic no-escalation theorem follows: the same gazette, with the same kernel verdicts, escalates or does not according to whether the permission reads what the act puts in force. Two results survive and both are inherited from the kernel's typing — no jurisdictional self-ratification, from strict pre-state evaluation and freshness, and monotone reach conditional on no widening, whose hypothesis a constitution declines on purpose.

Grounded Replay is unchanged and remains `GROUNDED-REPLAY-KERNEL-STABLE`: the
kernel does not import the Proper Exercise analysis, has no capability notion, and
its premises hold on every constitution here — including the one that escalates.

**The question this pass was dispatched to settle** was whether Proper Exercise is
its own mathematical module or the place where substantive normative content
necessarily enters. It is the second, and the evidence is a pair: two
constitutions with the same base and the same edit, identical in grounds,
disposals, issued content and declared evidence, both satisfying every premise and
every corollary of the kernel. One refuses the act. The other accepts it and the
state gains a capability nobody licensed. The only difference is whether the
permission relation reads what the act puts in force.

So a theorem of the form *proper transitions imply no unauthorized privilege
escalation* would have to quantify over permission relations, and no such
statement is true.

What survives is worth having and is small:

```text
E2  no jurisdictional self-ratification    theorem, over every capability
                                           assignment, from strict pre-state
                                           evaluation and freshness
E4  no widening gives monotone reach       theorem about a class of permission
                                           relations; the hypothesis is what a
                                           constitution declines when it means
                                           to allow amendment
```

Both are inherited from the kernel's typing rather than earned by any structure on
permission, and E4's hypothesis is exactly the naive subset rule for delegation —
available as a conditional, false as an axiom.

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

- `LEGITIMATE_EVOLUTION.md` — the minimal statement, then the layers.
- `PROPER_EXERCISE.md` — the fourteen separations, and why there is no
  no-escalation theorem.
- `CROSS_PROCESS_INTERFACE.md` — origin, historical and current, and what each costs.
- `CONSUMER_TEST.md` — deference, and which of the three it needs.
- `TRADERIZATION_CONSUMER.md` — enforcement, and the four repeal cases.
- `COUNTERMODELS.md` — every premise prosecuted; withdrawals are §§1-5.
- `THEOREM_MAP.md` — every claim graded, withdrawals first.
- `src/` — `replay.py` (the kernel), `office.py` (the semantics and a
  constitution model importing only the kernel), `ri_frame.py` (extraction from a
  record), `exercise.py` (capability and reach, an analysis over frames),
  `cases.py` (records the Carroll round did not have).
- `tests/` — 85 cases. `python3 tests/run.py`.

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
