"""Mediation as alphabet completeness, and where it stops composing.

A body `B` is a finite set of traces over an action alphabet.  A world semantics
`effect(action) -> set of authority effects` says which actions actually touch the
principal's authority.  A monitor over a *declared* authority alphabet `Sigma_auth`
blocks any declared action that is not principal-authorized.

  Mediates(M, B)      every action of B with a *declared* authority effect is in
                      Sigma_auth (so it passes through M).
  AuthoritySafe(M∘B)  no surviving trace has an unauthorized *actual* authority effect.

The theorem `Mediates ∧ POverride ⇒ AuthoritySafe` holds exactly when the declared
effects equal the actual effects — alphabet completeness — and fails otherwise.
`joint_effect` models an effect two individually inert actions produce together.
"""
from __future__ import annotations


def monitor(traces, sigma_auth, authorized):
    """Keep traces whose every declared-authority action is authorized; a blocked action
    truncates the trace there (the monitor is an edit automaton that halts)."""
    out = []
    for tr in traces:
        kept = []
        for a in tr:
            if a in sigma_auth and a not in authorized:
                break
            kept.append(a)
        out.append(tuple(kept))
    return out


def mediates(traces, sigma_auth, declared_effect):
    return all(a in sigma_auth for tr in traces for a in tr if declared_effect(a))


def authority_safe(traces, actual_effect, authorized, joint_effect=None):
    for tr in traces:
        for a in tr:
            if actual_effect(a) and a not in authorized:
                return False
        if joint_effect is not None and joint_effect(tr):
            return False
    return True
