"""L0, channel confinement: the world component evolves by e alone.  A condition
on the transition function the principal faces, not on the realized world trace:
the consequence map of every baseline option at every decision point is e's, and
no world change occurs that e does not schedule."""
from __future__ import annotations


def l0(run, e):
    failures = []
    for t, ev in enumerate(e):
        if ev.decide is None:
            continue
        faced = run.faced.get(t, {})
        for opt, cons in ev.decide.options.items():
            if faced.get(opt) != cons:
                failures.append((t, opt))
    if run.world_writes and not failures:
        failures.append(("world", "direct"))
    return failures


def holds(runs, e):
    return {name: l0(r, e) for name, r in runs.items() if l0(r, e)}
