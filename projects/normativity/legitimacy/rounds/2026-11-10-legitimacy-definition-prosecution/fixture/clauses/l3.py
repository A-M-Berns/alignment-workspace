"""L3, ownership: the seed is the principal's by fiat; a later standards state is
hers iff the previous one was and the step was autonomous or licensed at the
pre-state.  The run map tracks the inductive predicate; this reads its trace."""
from __future__ import annotations


def l3(run):
    return [t for t, owned in enumerate(run.owned_trace) if not owned]


def holds(runs):
    return {name: l3(r) for name, r in runs.items() if l3(r)}
