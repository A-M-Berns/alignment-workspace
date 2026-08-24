"""Boundary fixture: the full-stack contract around the service core.

    obligation --> InquiryRequest --> CIS --> ServiceCertificate
        --> record/account boundary (ValidCert AND MayClose)
        --> ServiceEvent in the record --> assessment consumes the event

Two sides live in this module, deliberately separated:

- `serve` is the CIS side: interaction plus certificate production.
  CIS does not close obligations; it produces evidence of adequate
  service. It never sees why an obligation arose, its discharge rules,
  or any downstream interpretation machinery (the test suite enforces
  this at the source level with a vocabulary scan on `service_core`).
- `Obligation`, `may_close` policies, `record_service`, and
  `ServiceEvent` are minimal RECORD-SIDE stubs: the account layer that
  decides whether a valid certificate presently discharges an
  obligation, and that owns the historical fact "this obligation was
  accounted as serviced by this certificate." Assessment consumes that
  recorded event, never a raw completion claim by the controller.
"""
from __future__ import annotations

from dataclasses import dataclass

from service_core import (InquiryRequest, ServiceCertificate, ServiceSpec,
                          transcript_of)


# ---------------------------------------------------------------------------
# CIS side
# ---------------------------------------------------------------------------

def serve(requests, specs, env, policy, horizon):
    """Drive `policy` against `env`, then produce a valid certificate
    for each request whose pinned spec's prover can witness it.
    Returns (history, certs) where certs maps each obligation_id to a
    valid ServiceCertificate or None.

    Validity is the only judgment made here. Whether upstream may
    presently close anything on a certificate is not this function's
    question, so a certificate is returned even when every discharge
    policy would refuse it.
    """
    history = ()
    for _ in range(horizon):
        action = policy(history)
        if action is None:
            break
        response = env.pick(history, action)
        history = history + ((action, response),)

    transcript = transcript_of(history)
    certs = {}
    for req in requests:
        spec = specs[req.spec_id]
        cert = spec.prove(transcript)
        certs[req.obligation_id] = (
            cert if cert is not None and spec.check(transcript, cert)
            else None)
    return history, certs


class ScriptedEnv:
    """Deterministic pick over a relational env, for fixtures."""

    def __init__(self, env, choose=min):
        self.env = env
        self.choose = choose

    def pick(self, history, action):
        return self.choose(sorted(self.env.responses(history, action),
                                  key=repr))


# ---------------------------------------------------------------------------
# Record-side stubs (account layer; NOT part of the service core)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Obligation:
    """Record-side: the full obligation, with everything the service
    layer must not see. `to_request()` is the projection that crosses
    the boundary."""
    oid: str
    spec_id: str
    accrued_at: int
    origin: str

    def to_request(self) -> InquiryRequest:
        return InquiryRequest(self.oid, self.spec_id)


@dataclass(frozen=True)
class ServiceEvent:
    """The historical normative fact, owned by the record: this
    obligation was accounted as serviced by this certificate."""
    event_id: str
    obligation_id: str
    certificate: ServiceCertificate


def always_close(now, cert, cited, obligation):
    return True


def freshness_close(window):
    """A discharge policy: the certificate's newest cited receipt must
    be within `window` steps of now. A policy about DISCHARGE — it can
    refuse a certificate whose historical validity is untouched."""
    def may_close(now, cert, cited, obligation):
        return cited and now - max(r.index for r in cited) <= window
    return may_close


def record_service(record, transcript, spec, obligation, cert, now,
                   may_close):
    """The account boundary: mint a ServiceEvent iff the certificate is
    valid for the obligation's pinned spec AND the discharge policy
    presently admits it. Refusal leaves both the certificate's validity
    and the obligation's openness untouched."""
    if spec.spec_id != obligation.spec_id:
        return None
    if not spec.check(transcript, cert):
        return None
    cited = tuple(transcript[i] for i in cert.cited)
    if not may_close(now, cert, cited, obligation):
        return None
    event = ServiceEvent(f"s{len(record)}", obligation.oid, cert)
    record.append(event)
    return event
