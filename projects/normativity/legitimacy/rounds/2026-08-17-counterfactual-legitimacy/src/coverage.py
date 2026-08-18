"""Inquiry coverage: the property comparing policies cannot express.

`noncapture.access` compares advisor policies against one another, so it passes
whenever the class is uniform. If every policy in the class withholds the same
due reason, the delivered due streams are identical, the clause is satisfied, and
the process never sees the thing it was owed.

That is not a defect in the clause. Anti-selection and adequacy are different
properties and the round keeps them apart:

```
advisor cannot select access     a relation between policies
the process has adequate access  a relation between one run and what was due
```

`coverage` is the second. It is not counterfactual, not advisor-relative, and it
is the one clause of the interface that a single realized run determines — which
is also why it cannot do the first one's job.
"""

from __future__ import annotations

from typing import Sequence

from fixture import Fixture, Policy, Run


def undelivered(fixture: Fixture, policy: Policy) -> tuple[tuple[int, tuple], ...]:
    """Due inputs that never reached the process on this run."""
    out = []
    for step in range(len(fixture.plan)):
        pool = fixture.due_pool.get(step, frozenset())
        given = {item.key() for item in policy.items(step)}
        missing = pool - given
        if missing:
            out.append((step, tuple(sorted(missing))))
    return tuple(out)


def unarisen(fixture: Fixture, policy: Policy) -> tuple[int, ...]:
    """Encounters the fixture declares and this run did not have."""
    return tuple(sorted(policy.suppress_encounters))


def unserviced(run: Run) -> tuple[str, ...]:
    """Due substances the environment says arose and the process never took up.

    Read off the same projection `L*` reads, so this is the part of the target
    that a record does determine — and it is exactly the part `L*` does not need
    an environment's `bears_on` or `settles` to adjudicate.
    """
    from conditions import project
    _uses, _discharges, confrontations = project(run.trajectory)
    taken = {c.demand_id for c in confrontations}
    missing = []
    for demand in run.environment.demands:
        if demand.entitled and demand.substance not in taken:
            missing.append(demand.substance)
    return tuple(sorted(set(missing)))


def coverage(fixture: Fixture, policy: Policy) -> tuple[str, ...]:
    """Whether this run had the access it was owed.

    Three failure codes, kept separate because they are three different things
    going wrong and a downstream theorem needs to know which.
    """
    codes: list[str] = []
    if undelivered(fixture, policy):
        codes.append("coverage.due_reason_never_delivered")
    if unarisen(fixture, policy):
        codes.append("coverage.encounter_never_arose")
    if unserviced(fixture.run(policy)):
        codes.append("coverage.due_demand_never_serviced")
    return tuple(sorted(set(codes)))


def covered(fixture: Fixture, variation: Sequence[Policy]) -> bool:
    """Coverage on every arm of the class. Distinct from `access`, which is
    satisfied by a class that fails this uniformly."""
    return not any(coverage(fixture, policy) for policy in variation)
