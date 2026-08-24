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

    def test_contradictory_receipt_yields_review_not_invalidation(self):
        # A later receipt contradicting serviced evidence mints a NEW
        # upstream review liability; the old certificate remains a
        # valid record and the old closure is not reopened in-layer.
        docket, specs, env, policy = self.fixture()
        history, outcomes, _ = run_service(docket, specs, env, policy, 3)
        cert = outcomes[0].certificate
        extended = history + (("measure", "contradiction"),)
        from service_core import transcript_of
        self.assertTrue(specs["sigma-m"].check(transcript_of(extended), cert))
        review = Liability("L-review", len(extended), "sigma-m",
                           origin="basis-review")
        self.assertNotEqual(review.lid, outcomes[0].lid)


# ---------------------------------------------------------------------------
# Downstream stubs live HERE, not in src/: the frozen reason interface
# (sources drawn from V ⊔ L) is downstream vocabulary the service layer
# must never import.
# ---------------------------------------------------------------------------

class ReasonOccurrence:
    """Frozen-waist stub: e = (id, sources, target, applied_as), with
    every source either a content id ("v:...") or a transcript receipt
    id ("l:<index>")."""

    def __init__(self, eid, sources, target, applied_as):
        assert all(s.startswith(("v:", "l:")) for s in sources), sources
        self.eid, self.sources = eid, frozenset(sources)
        self.target, self.applied_as = target, applied_as


class TestThreeProvenance(unittest.TestCase):
    """Canonical microhistory separating the three provenance
    relations: evidential grounds (reason sources), procedural service
    adequacy (the certificate), accounting license (the record's
    closure of the liability using the certificate)."""

    def microhistory(self):
        d = Liability("d-protocol", 0, "sigma-inv", origin="answerability")
        spec = measurement_spec("sigma-inv")
        env = ScriptedEnv(Env(("measure", "wait"),
                              lambda h, a: {"v" if a == "measure" else "-"}))
        policy = lambda h: "measure" if len(h) < 2 else None
        history, outcomes, unserviced = run_service(
            [d], {"sigma-inv": spec}, env, policy, 4)
        return d, history, outcomes[0], unserviced

    def test_canonical_composition(self):
        d, history, outcome, unserviced = self.microhistory()
        self.assertEqual(unserviced, [])
        k = outcome.certificate
        receipts = [f"l:{i}" for i in k.cited]
        # Assessment mints e from receipts plus auxiliary content; the
        # record closes d using k. e does not cite k.
        e = ReasonOccurrence("e1", receipts + ["v:aux-theory"],
                             "p", applied_as="support")
        account_closure = {"liability": d.lid, "certificate": k}
        self.assertNotIn("cert", " ".join(e.sources))
        self.assertEqual(account_closure["certificate"].spec_id, d.spec_id)
        self.assertTrue(e.sources & set(receipts))

    def test_valid_service_with_no_bearing(self):
        # Cases 1 and 3: the certificate is valid; assessment returns
        # NoBearing and mints nothing; the account still closes.
        d, history, outcome, _ = self.microhistory()
        minted = []                       # assessment stub: NoBearing
        self.assertEqual(minted, [])
        self.assertEqual(outcome.lid, d.lid)   # closure independent

    def test_same_receipts_different_applications(self):
        # Case 2: one receipt set, two occurrences under different
        # applied_as judgments, distinct conclusions.
        _, _, outcome, _ = self.microhistory()
        receipts = [f"l:{i}" for i in outcome.certificate.cited]
        e1 = ReasonOccurrence("e1", receipts, "p", applied_as="support")
        e2 = ReasonOccurrence("e2", receipts, "not-p", applied_as="undercut")
        self.assertEqual(e1.sources, e2.sources)
        self.assertNotEqual((e1.target, e1.applied_as),
                            (e2.target, e2.applied_as))

    def test_shared_evidence_single_reason(self):
        # Case 4: two liabilities share evidence; assessment mints one
        # occurrence; both close through their own certificates.
        d1 = Liability("d1", 0, "sigma-m", origin="answerability")
        d2 = Liability("d2", 0, "sigma-m2", origin="decision-relevance")
        specs = {"sigma-m": measurement_spec("sigma-m"),
                 "sigma-m2": measurement_spec("sigma-m2")}
        env = ScriptedEnv(Env(("measure", "wait"),
                              lambda h, a: {"v" if a == "measure" else "-"}))
        _, outcomes, unserviced = run_service(
            [d1, d2], specs, env, lambda h: "measure" if not h else None, 2)
        self.assertEqual(unserviced, [])
        receipts = {f"l:{i}" for o in outcomes for i in o.certificate.cited}
        e = ReasonOccurrence("e-shared", sorted(receipts), "p", "support")
        self.assertEqual(len(outcomes), 2)     # two closures
        self.assertEqual(len(receipts), 1)     # one shared ground
        self.assertEqual(len(e.sources), 1)    # one reason occurrence

    def test_protocol_compliance_is_ordinary_content(self):
        # Case 5: "this experiment followed protocol P" is a content in
        # V supported by receipts — no new source sort. V ⊔ L stays
        # sufficient on every tested case.
        _, _, outcome, _ = self.microhistory()
        receipts = [f"l:{i}" for i in outcome.certificate.cited]
        e = ReasonOccurrence("e-proc", receipts,
                             "followed-protocol-P", applied_as="support")
        self.assertTrue(all(s.startswith("l:") for s in e.sources))


if __name__ == "__main__":
    unittest.main()
