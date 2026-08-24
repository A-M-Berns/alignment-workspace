"""End-to-end boundary fixture:

    upstream Due/InquiryLiability -> service controller -> action ->
    environment response -> immutable receipt(s) -> ServiceCert ->
    downstream opaque Assess handoff.

Two upstream origins (answerability-generated and decision-relevance-
generated) must be indistinguishable to the service layer; the service
sources must not mention stance, reason-ledger, or authority structure;
the assessment stub must not need Gamma or scheduling internals."""
import pathlib
import re
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from composition import ScriptedEnv, ServiceOutcome, run_service
from service_core import Certificate, Env, Liability, ServiceSpec

SRC = pathlib.Path(__file__).resolve().parents[1] / "src"


def measurement_spec(sid):
    def check(cited, data):
        return len(cited) == 1 and cited[0].action == "measure"

    def make(transcript):
        for r in transcript:
            if r.action == "measure":
                return Certificate(sid, (r.index,))
        return None
    return ServiceSpec(sid, check, make)


class AssessStub:
    """Downstream consumer: records handoffs; sees receipts and
    certificates only."""

    def __init__(self):
        self.received = []

    def take(self, outcome: ServiceOutcome):
        assert isinstance(outcome, ServiceOutcome)
        self.received.append((outcome.lid, outcome.certificate.spec_id,
                              outcome.certificate.cited))


class TestBoundary(unittest.TestCase):
    def fixture(self):
        # Upstream mints liabilities from two different origins; the
        # service layer receives the same type either way.
        d_ans = Liability("L-ans", 0, "sigma-m", origin="answerability")
        d_dec = Liability("L-dec", 0, "sigma-m2", origin="decision-relevance")
        specs = {"sigma-m": measurement_spec("sigma-m"),
                 "sigma-m2": measurement_spec("sigma-m2")}
        env = ScriptedEnv(Env(("measure", "wait"),
                              lambda h, a: {"v" if a == "measure" else "-"}))
        policy = lambda h: "measure" if len(h) < 1 else None
        return [d_ans, d_dec], specs, env, policy

    def test_pipeline_produces_receipts_certs_and_handoff(self):
        docket, specs, env, policy = self.fixture()
        history, outcomes, unserviced = run_service(
            docket, specs, env, policy, horizon=3)
        self.assertEqual(unserviced, [])
        self.assertEqual(len(outcomes), 2)
        assess = AssessStub()
        for o in outcomes:
            assess.take(o)
        # Shared evidence, distinct closures (microcase 4 end-to-end):
        (l1, s1, c1), (l2, s2, c2) = assess.received
        self.assertNotEqual(l1, l2)
        self.assertEqual(c1, c2)

    def test_origins_indistinguishable_to_service(self):
        docket, specs, env, policy = self.fixture()
        flipped = [Liability(d.lid, d.accrued_at, d.spec_id, "swapped")
                   for d in docket]
        h1, o1, u1 = run_service(docket, specs, env, policy, 3)
        h2, o2, u2 = run_service(flipped, specs, env, policy, 3)
        self.assertEqual(h1, h2)
        self.assertEqual([(o.lid, o.certificate) for o in o1],
                         [(o.lid, o.certificate) for o in o2])

    def test_service_sources_do_not_touch_upstream_or_downstream(self):
        forbidden = re.compile(
            r"\bstance\b|reason[_ ]?ledger|authority|belief|credal"
            r"|docket[_ ]?rule", re.IGNORECASE)
        for name in ("service_core.py", "composition.py", "embeddings.py"):
            text = (SRC / name).read_text()
            hits = [ln for ln in text.splitlines() if forbidden.search(ln)]
            self.assertEqual(hits, [], (name, hits))

    def test_history_is_append_only_through_the_run(self):
        docket, specs, env, policy = self.fixture()
        history, outcomes, _ = run_service(docket, specs, env, policy, 3)
        for o in outcomes:
            for r in o.cited_receipts:
                self.assertEqual(history[r.index],
                                 (r.action, r.response))


if __name__ == "__main__":
    unittest.main()
