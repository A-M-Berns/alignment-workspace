"""End-to-end boundary fixture for the full-stack contract:

    obligation -> InquiryRequest -> CIS -> ServiceCertificate
        -> record boundary (ValidCert AND MayClose) -> ServiceEvent
        -> assessment consumes the recorded event.

CIS does not close obligations; it produces evidence of adequate
service. The record decides what a certificate accounts for."""
import pathlib
import re
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from composition import (Obligation, ScriptedEnv, ServiceEvent,
                         always_close, freshness_close, record_service,
                         serve)
from service_core import (Env, InquiryRequest, ServiceCertificate,
                          ServiceSpec, transcript_of)

SRC = pathlib.Path(__file__).resolve().parents[1] / "src"


def measurement_spec(sid):
    def check(cited, data):
        return len(cited) == 1 and cited[0].action == "measure"

    def prover(transcript):
        for r in transcript:
            if r.action == "measure":
                return ServiceCertificate(sid, (r.index,))
        return None
    return ServiceSpec(sid, check, prover)


def measure_env():
    return ScriptedEnv(Env(("measure", "wait"),
                           lambda h, a: {"v" if a == "measure" else "-"}))


class TestBoundary(unittest.TestCase):
    def fixture(self):
        # Record-side obligations from two origins; CIS receives only
        # their InquiryRequest projections — origin is excluded by
        # type, not convention.
        o_ans = Obligation("o-ans", "sigma-m", 0, "answerability")
        o_dec = Obligation("o-dec", "sigma-m2", 0, "decision-relevance")
        specs = {"sigma-m": measurement_spec("sigma-m"),
                 "sigma-m2": measurement_spec("sigma-m2")}
        policy = lambda h: "measure" if len(h) < 1 else None
        return [o_ans, o_dec], specs, measure_env(), policy

    def test_cis_produces_certificates_not_closures(self):
        obligations, specs, env, policy = self.fixture()
        requests = [o.to_request() for o in obligations]
        history, certs = serve(requests, specs, env, policy, 3)
        self.assertTrue(all(c is not None for c in certs.values()))
        # Shared evidence, distinct certificates (microcase 4 shape):
        self.assertEqual(certs["o-ans"].cited, certs["o-dec"].cited)
        self.assertNotEqual(certs["o-ans"].spec_id, certs["o-dec"].spec_id)

    def test_origin_excluded_by_type(self):
        obligations, *_ = self.fixture()
        req = obligations[0].to_request()
        self.assertEqual(set(req.__dataclass_fields__),
                         {"obligation_id", "spec_id"})

    def test_record_refuses_when_may_close_false(self):
        # CIS returns a valid certificate even though every discharge
        # attempt is refused; refusal creates no ServiceEvent and does
        # not disturb validity.
        obligations, specs, env, policy = self.fixture()
        o = obligations[0]
        history, certs = serve([o.to_request()], specs, env, policy, 3)
        cert = certs[o.oid]
        self.assertIsNotNone(cert)
        transcript = transcript_of(history)
        record = []
        never = lambda now, cert, cited, obligation: False
        event = record_service(record, transcript, specs[o.spec_id], o,
                               cert, len(transcript), never)
        self.assertIsNone(event)
        self.assertEqual(record, [])
        self.assertTrue(specs[o.spec_id].check(transcript, cert))

    def test_same_certificate_accepted_or_refused_by_policy(self):
        # The discharge policy alone decides; ValidCert never moves.
        obligations, specs, env, policy = self.fixture()
        o = obligations[0]
        history, certs = serve([o.to_request()], specs, env, policy, 3)
        cert = certs[o.oid]
        aged = history + (("wait", "-"),) * 5
        transcript = transcript_of(aged)
        spec = specs[o.spec_id]
        self.assertTrue(spec.check(transcript, cert))
        fresh_events, open_events = [], []
        refused = record_service(fresh_events, transcript, spec, o, cert,
                                 len(transcript), freshness_close(2))
        granted = record_service(open_events, transcript, spec, o, cert,
                                 len(transcript), always_close)
        self.assertIsNone(refused)
        self.assertIsInstance(granted, ServiceEvent)
        self.assertTrue(spec.check(transcript, cert))

    def test_shared_evidence_two_obligations_two_events(self):
        # One receipt can account for two obligations when the
        # discharge policy allows sharing; the obligations and their
        # ServiceEvents stay distinct.
        obligations, specs, env, policy = self.fixture()
        requests = [o.to_request() for o in obligations]
        history, certs = serve(requests, specs, env, policy, 3)
        transcript = transcript_of(history)
        record = []
        for o in obligations:
            event = record_service(record, transcript, specs[o.spec_id],
                                   o, certs[o.oid], len(transcript),
                                   always_close)
            self.assertIsNotNone(event)
        self.assertEqual(len(record), 2)
        self.assertEqual(record[0].certificate.cited,
                         record[1].certificate.cited)
        self.assertNotEqual(record[0].obligation_id,
                            record[1].obligation_id)

    def test_service_core_blind_to_record_and_downstream(self):
        # No source file mentions downstream normative vocabulary; and
        # the service core carries NO code identifier for record-side
        # notions (its docstrings may say discharge lives elsewhere;
        # nothing in it implements discharge). Checked over the AST.
        import ast
        downstream = re.compile(
            r"\bstance\b|reason[_ ]?ledger|authority|belief|credal"
            r"|docket[_ ]?rule", re.IGNORECASE)
        for name in ("service_core.py", "composition.py", "embeddings.py"):
            text = (SRC / name).read_text()
            hits = [ln for ln in text.splitlines() if downstream.search(ln)]
            self.assertEqual(hits, [], (name, hits))
        record_side = re.compile(
            r"mayclose|may_close|serviceevent|normativerecord|discharge"
            r"|admit|admissible|origin", re.IGNORECASE)
        idents = set()
        for node in ast.walk(ast.parse((SRC / "service_core.py").read_text())):
            for field in ("id", "attr", "name", "arg", "module"):
                v = getattr(node, field, None)
                if isinstance(v, str):
                    idents.add(v)
        bad = sorted(i for i in idents if record_side.search(i))
        self.assertEqual(bad, [], bad)

    def test_contradictory_receipt_yields_review_not_invalidation(self):
        # A later receipt contradicting serviced evidence mints a NEW
        # record-side obligation; the old certificate remains a valid
        # record and the old ServiceEvent stands.
        obligations, specs, env, policy = self.fixture()
        o = obligations[0]
        history, certs = serve([o.to_request()], specs, env, policy, 3)
        record = []
        record_service(record, transcript_of(history), specs[o.spec_id],
                       o, certs[o.oid], len(history), always_close)
        extended = history + (("measure", "contradiction"),)
        self.assertTrue(specs[o.spec_id].check(transcript_of(extended),
                                               certs[o.oid]))
        review = Obligation("o-review", "sigma-m", len(extended),
                            "basis-review")
        self.assertNotEqual(review.oid, o.oid)
        self.assertEqual(len(record), 1)


# ---------------------------------------------------------------------------
# Downstream stubs live HERE, not in src/: the frozen reason interface
# (sources drawn from V ⊔ L) is downstream vocabulary the service layer
# must never import. Assessment consumes the RECORDED ServiceEvent.
# ---------------------------------------------------------------------------

class ReasonOccurrence:
    """Frozen-waist stub: e = (id, sources, target, applied_as), with
    every source either a content id ("v:...") or a transcript receipt
    id ("l:<index>")."""

    def __init__(self, eid, sources, target, applied_as):
        assert all(s.startswith(("v:", "l:")) for s in sources), sources
        self.eid, self.sources = eid, frozenset(sources)
        self.target, self.applied_as = target, applied_as


def assess(event: ServiceEvent, transcript, verdicts):
    """Assessment stub: consumes a RECORDED service event (not a raw
    controller claim), reads the cited receipts, and either mints
    occurrence specs or returns no bearing."""
    receipts = [f"l:{i}" for i in event.certificate.cited]
    out = []
    for (target, applied_as) in verdicts:
        out.append(ReasonOccurrence(f"e-{event.event_id}-{target}",
                                    receipts, target, applied_as))
    return out


class TestThreeProvenance(unittest.TestCase):
    """Canonical microhistory separating the three provenance
    relations: evidential grounds (reason sources), procedural service
    adequacy (the certificate), accounting license (the record's
    ServiceEvent discharging the obligation with the certificate)."""

    def microhistory(self):
        o = Obligation("o-protocol", "sigma-inv", 0, "answerability")
        specs = {"sigma-inv": measurement_spec("sigma-inv")}
        policy = lambda h: "measure" if len(h) < 2 else None
        history, certs = serve([o.to_request()], specs, measure_env(),
                               policy, 4)
        transcript = transcript_of(history)
        record = []
        event = record_service(record, transcript, specs["sigma-inv"], o,
                               certs[o.oid], len(transcript), always_close)
        return o, transcript, certs[o.oid], event

    def test_canonical_composition(self):
        o, transcript, kappa, s = self.microhistory()
        self.assertIsInstance(s, ServiceEvent)
        # Assessment consumes the recorded event and mints e citing
        # receipts (plus auxiliary content) — never kappa itself.
        (e,) = assess(s, transcript, [("p", "support")])
        e = ReasonOccurrence(e.eid, e.sources | {"v:aux-theory"},
                             e.target, e.applied_as)
        receipts = {f"l:{i}" for i in kappa.cited}
        self.assertTrue(receipts <= e.sources)
        self.assertTrue(all(x.startswith(("v:", "l:")) for x in e.sources))
        # The three provenance relations differ:
        self.assertEqual(s.certificate, kappa)        # accounting uses kappa
        self.assertNotIn(kappa.spec_id,               # e does not cite it
                         {x.split(":", 1)[1] for x in e.sources})

    def test_assessment_requires_recorded_event(self):
        # No ServiceEvent, no assessment: a raw CIS certificate is not
        # assessment input in this contract.
        o, transcript, kappa, _ = self.microhistory()
        record = []
        refused = record_service(record, transcript,
                                 measurement_spec("sigma-inv"), o, kappa,
                                 len(transcript),
                                 lambda *a: False)
        self.assertIsNone(refused)          # nothing for assess() to take

    def test_valid_service_with_no_bearing(self):
        # The event is recorded; assessment returns NoBearing and mints
        # nothing; discharge is unaffected. Service adequacy does not
        # entail epistemic bearing.
        o, transcript, kappa, s = self.microhistory()
        minted = assess(s, transcript, [])
        self.assertEqual(minted, [])
        self.assertIsInstance(s, ServiceEvent)

    def test_same_receipts_different_applications(self):
        # One receipt set, two occurrences under different applied_as
        # judgments, distinct conclusions.
        o, transcript, kappa, s = self.microhistory()
        e1, e2 = assess(s, transcript,
                        [("p", "support"), ("not-p", "undercut")])
        self.assertEqual(e1.sources, e2.sources)
        self.assertNotEqual((e1.target, e1.applied_as),
                            (e2.target, e2.applied_as))

    def test_shared_evidence_single_reason(self):
        # Two obligations share evidence; both discharge through their
        # own certificates and events; assessment mints one occurrence.
        o1 = Obligation("o1", "sigma-m", 0, "answerability")
        o2 = Obligation("o2", "sigma-m2", 0, "decision-relevance")
        specs = {"sigma-m": measurement_spec("sigma-m"),
                 "sigma-m2": measurement_spec("sigma-m2")}
        history, certs = serve([o.to_request() for o in (o1, o2)], specs,
                               measure_env(),
                               lambda h: "measure" if not h else None, 2)
        transcript = transcript_of(history)
        record = []
        for o in (o1, o2):
            self.assertIsNotNone(record_service(
                record, transcript, specs[o.spec_id], o, certs[o.oid],
                len(transcript), always_close))
        self.assertEqual(len(record), 2)
        (e,) = assess(record[0], transcript, [("p", "support")])
        self.assertEqual(len(e.sources), 1)     # one shared ground

    def test_protocol_compliance_is_ordinary_content(self):
        # "This experiment followed protocol P" is a content in V
        # supported by receipts — no new source sort; V ⊔ L suffices.
        o, transcript, kappa, s = self.microhistory()
        (e,) = assess(s, transcript, [("followed-protocol-P", "support")])
        self.assertTrue(all(x.startswith("l:") for x in e.sources))


if __name__ == "__main__":
    unittest.main()
