"""Boundary fixture: upstream record -> service controller -> downstream
assessment, with the service layer blind to why liabilities exist and to
what serviced evidence means.

The controller consumes `Liability` objects (opaque origin), drives the
environment, appends receipts to the append-only transcript, certifies
against each liability's pinned spec, and emits `ServiceOutcome`
handoffs. It never sees upstream normative state or downstream
interpretation machinery; the test suite enforces this at the source
level with a vocabulary scan.
"""
from __future__ import annotations

from dataclasses import dataclass

from service_core import Certificate, Liability, ServiceSpec, transcript_of


@dataclass(frozen=True)
class ServiceOutcome:
    """Downstream handoff: which liability, which certificate, over
    which receipts. Interpretation is downstream's business."""
    lid: str
    certificate: Certificate
    cited_receipts: tuple


def run_service(docket, specs, env, policy, horizon):
    """Drive `policy` against `env` for up to `horizon` steps, then
    certify every docket liability its pinned spec accepts.

    - `docket`: iterable of Liability (origin is opaque data).
    - `specs`: spec_id -> ServiceSpec (the pinned specifications).
    - `policy`: history -> action.
    - Environment responses here are resolved by `env.pick(h, a)`
      (tests use deterministic or scripted picks; adversarial analysis
      lives in the game solver, not in this fixture).

    Returns (history, outcomes, unserviced_ids).
    """
    history = ()
    for _ in range(horizon):
        action = policy(history)
        if action is None:
            break
        response = env.pick(history, action)
        history = history + ((action, response),)

    transcript = transcript_of(history)
    outcomes, unserviced = [], []
    for d in docket:
        spec = specs[d.spec_id]
        cert = spec.prove(transcript)
        if (cert is not None and spec.check(transcript, cert)
                and spec.admissible(transcript, cert)):
            # Closure handoff requires BOTH a valid historical
            # certificate and present admissibility; a valid but
            # lapsed certificate stays a true record without
            # discharging the open liability.
            cited = tuple(transcript[i] for i in cert.cited)
            outcomes.append(ServiceOutcome(d.lid, cert, cited))
        else:
            unserviced.append(d.lid)
    return history, outcomes, unserviced


class ScriptedEnv:
    """Deterministic pick over a relational env, for fixtures."""

    def __init__(self, env, choose=min):
        self.env = env
        self.choose = choose

    def pick(self, history, action):
        return self.choose(sorted(self.env.responses(history, action),
                                  key=repr))
