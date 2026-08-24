"""The ten mandatory adversarial microcases. Each is expressed in the
generic interface without new normative primitives; where a case leaves
a prior model's subclass, the violated capability is checked."""
import itertools
import pathlib
import sys
import unittest
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from service_core import (ServiceCertificate, Env, FiniteStateEnv, InquiryRequest,
                          Monitor, ServiceSpec, fixed_realization_family,
                          is_submodular, jointly_servable,
                          order_irrelevant, prover_certified,
                          repetition_irrelevant, servable, transcript_of)
from embeddings import GKInstance, gk_certified, gk_self_certifying, \
    gk_semantic


def visited_set_spec(spec_id, predicate):
    """Set-factorizing spec: certified iff predicate(visited actions)."""
    def check(cited, data):
        return predicate(frozenset(r.action for r in cited))

    def make(transcript):
        for k in range(len(transcript) + 1):
            cited = tuple(range(k))
            if predicate(frozenset(transcript[i].action for i in cited)):
                return ServiceCertificate(spec_id, cited)
        return None
    return ServiceSpec(spec_id, check, make)


class TestComplementarity(unittest.TestCase):
    # 1. Neither a nor b suffices; {a, b} does.
    def test_valid_service_but_not_submodular(self):
        spec = visited_set_spec("both", lambda s: {"a", "b"} <= s)
        t = transcript_of((("a", "."), ("b", ".")))
        self.assertTrue(prover_certified(spec, t))
        for h in [(("a", "."),), (("b", "."),)]:
            self.assertFalse(prover_certified(spec, transcript_of(h)))
        # Progress 1 iff both present is not submodular.
        f = lambda s: Fraction(1) if {"a", "b"} <= s else Fraction(0)
        self.assertFalse(is_submodular(f, ("a", "b")))
        self.assertTrue(order_irrelevant(
            spec, [(), (("a", "."),), (("b", "."),),
                   (("a", "."), ("b", ".")), (("b", "."), ("a", "."))]))


class TestResponseDependentBranching(unittest.TestCase):
    # 2. After a, the useful follow-up depends on the response; the
    # wrong follow-up is dead, so no fixed action sequence wins.
    def make_env(self):
        def delta(s, a):
            if s == "s0" and a == "a":
                return {("y1", "s1"), ("y2", "s2")}
            if s == "s1" and a == "b":
                return {("ok", "done")}
            if s == "s2" and a == "c":
                return {("ok", "done")}
            return {("na", "dead")}
        return FiniteStateEnv(("a", "b", "c"), "s0", delta)

    def test_adaptive_wins_no_fixed_sequence_does(self):
        env = self.make_env()
        mon = Monitor({"i", "acc"}, "i",
                      lambda m, a, y: "acc" if y == "ok" else m, {"acc"})
        self.assertTrue(servable(env, mon))
        for n in range(4):
            for seq in itertools.product(env.actions, repeat=n):
                self.assertTrue(self.some_run_fails(env, mon, seq))

    def some_run_fails(self, env, mon, seq):
        def runs(h, i):
            if i == len(seq):
                return [h]
            out = []
            for y in env.responses(h, seq[i]):
                out.extend(runs(h + ((seq[i], y),), i + 1))
            return out
        return any(not mon.certified(h) for h in runs((), 0))


class TestIntervention(unittest.TestCase):
    # 3. Performing a changes what b later observes: no fixed
    # realization presents Gamma, yet the instance is ordinary service.
    def make_env(self):
        def responses(h, a):
            if a == "b":
                return {"1"} if any(x == "a" for x, _ in h) else {"0"}
            return {"done"}
        return Env(("a", "b"), responses)

    def test_no_fixed_realization_presentation(self):
        env = self.make_env()
        self.assertIsNone(fixed_realization_family(env, 2))

    def test_still_ordinary_service(self):
        env = self.make_env()
        spec = visited_set_spec("touch-b", lambda s: "b" in s)
        h = (("a", "done"), ("b", "1"))
        self.assertEqual(env.responses((("a", "done"),), "b"),
                         frozenset({"1"}))
        self.assertTrue(prover_certified(spec, transcript_of(h)))


class TestSharedEvidence(unittest.TestCase):
    # 4. One receipt appears in certificates for two distinct
    # liabilities; the liabilities stay distinct.
    def test_one_receipt_two_liabilities(self):
        d1 = InquiryRequest("d1", "sigma1")
        d2 = InquiryRequest("d2", "sigma2")
        self.assertNotEqual(d1, d2)

        def make_spec(sid):
            def check(cited, data):
                return len(cited) == 1 and cited[0].action == "measure"

            def make(transcript):
                for r in transcript:
                    if r.action == "measure":
                        return ServiceCertificate(sid, (r.index,))
                return None
            return ServiceSpec(sid, check, make)

        t = transcript_of((("measure", "v"),))
        c1 = make_spec("sigma1").prove(t)
        c2 = make_spec("sigma2").prove(t)
        self.assertEqual(c1.cited, c2.cited)          # shared receipt
        self.assertNotEqual(c1.spec_id, c2.spec_id)   # separate closures


class TestSameTypeMultiplicity(unittest.TestCase):
    # 5. Two open occurrences with the SAME pinned spec content.
    # Whether one trace can close both is the spec's business; the
    # service layer never coalesces the occurrences.
    def sharing_spec(self, sid):
        def check(cited, data):
            return len(cited) == 1 and cited[0].action == "measure"

        def make(transcript):
            for r in transcript:
                if r.action == "measure":
                    return ServiceCertificate(sid, (r.index,))
            return None
        return ServiceSpec(sid, check, make)

    def exclusive_certs(self, transcript, n_occurrences):
        """Exclusive-evidence account rule: each occurrence must cite a
        measure receipt no other occurrence cites."""
        avail = [r.index for r in transcript if r.action == "measure"]
        return avail[:n_occurrences] if len(avail) >= n_occurrences else None

    def test_sharing_spec_closes_both(self):
        t = transcript_of((("measure", "v"),))
        c1 = self.sharing_spec("occ1").prove(t)
        c2 = self.sharing_spec("occ2").prove(t)
        self.assertTrue(self.sharing_spec("occ1").check(t, c1))
        self.assertTrue(self.sharing_spec("occ2").check(t, c2))

    def test_exclusive_rule_closes_only_one(self):
        t1 = transcript_of((("measure", "v"),))
        self.assertIsNone(self.exclusive_certs(t1, 2))
        self.assertIsNotNone(self.exclusive_certs(t1, 1))
        t2 = transcript_of((("measure", "v"), ("measure", "w")))
        self.assertIsNotNone(self.exclusive_certs(t2, 2))


class TestHiddenSuccessWithoutCertification(unittest.TestCase):
    # 6. The true realization satisfies the goal; a consistent
    # alternative does not; no certificate exists (GK Definition 7
    # fails), and the layer must not close on inaccessible truth.
    def make_instance(self):
        f_table = {
            ("good", frozenset()): Fraction(0),
            ("good", frozenset({"e"})): Fraction(1),
            ("bad", frozenset()): Fraction(0),
            ("bad", frozenset({"e"})): Fraction(0),
        }
        return GKInstance(
            items=("e",),
            realizations={"good": {"e": "s"}, "bad": {"e": "s"}},
            prior={"good": Fraction(1, 2), "bad": Fraction(1, 2)},
            f=lambda dom, n: f_table[(n, frozenset(dom))],
            quota=Fraction(1))

    def test_semantic_true_certificate_false(self):
        inst = self.make_instance()
        h = (("e", "s"),)                     # observation cannot split
        self.assertTrue(gk_semantic(inst, h, "good"))
        self.assertFalse(gk_certified(inst, h))
        self.assertFalse(gk_self_certifying(inst))


class TestOverload(unittest.TestCase):
    # 7. Every arrival individually serviceable; arrivals outpace
    # capacity. What overload defeats depends on where the deadline is
    # typed: a deadline in Check (receipt index within a window of
    # accrual — citation-local, so the induced Certifiable is still
    # monotone, just time-barred) defeats forceable certifiability
    # itself; a deadline in the record-side DISCHARGE policy defeats
    # timely closure while late historical certification remains
    # achievable; with no deadline, only bounded latency fails.
    def test_deadline_in_check_defeats_certifiability(self):
        # Two occurrences accrue per step, one action per step, and a
        # VALID certificate requires its receipt within 1 step of
        # accrual (an index constraint, citation-local). Horizon 3: 6
        # occurrences, at most 3 receipts, each certifying at most one
        # occurrence (exclusive evidence): every policy strands
        # someone. Checked exhaustively over all action schedules.
        horizon = 3
        occurrences = [(f"d{t}{i}", t) for t in range(horizon)
                       for i in range(2)]
        for schedule in itertools.product(
                [occ[0] for occ in occurrences], repeat=horizon):
            served = set()
            ok = True
            for step, target in enumerate(schedule):
                accrued = dict(occurrences)[target]
                if target not in served and accrued <= step <= accrued + 1:
                    served.add(target)
            ok = len(served) == len(occurrences)
            self.assertFalse(ok)

    def test_deadline_in_discharge_defeats_timely_closure_only(self):
        # Same overload, but the window is record-side discharge
        # policy, not validity: a dedicated receipt at any time makes
        # the occurrence historically certifiable, while the record
        # only discharges on a receipt within 1 step of accrual. Under
        # FIFO every occurrence is eventually certifiable, yet from
        # some occurrence on, none ever has a dischargeable moment:
        # overload defeats timely closure, not historical service.
        arrivals = {f"d{n}": n // 2 for n in range(12)}   # 2 per step
        service = {f"d{n}": n for n in range(12)}         # FIFO, capacity 1
        for lid, acc in arrivals.items():
            self.assertGreaterEqual(service[lid], acc)    # certifiable
        dischargeable = [lid for lid, acc in arrivals.items()
                         if service[lid] <= acc + 1]
        stranded = [lid for lid, acc in arrivals.items()
                    if service[lid] > acc + 1]
        self.assertEqual(dischargeable, ["d0", "d1", "d2"])
        self.assertGreater(len(stranded), 0)

    def test_fifo_eventual_service_with_diverging_wait(self):
        # Without deadlines, FIFO services every occurrence at a finite
        # time, while the waiting time of the n-th grows without bound:
        # eventual liveness survives overload; bounded latency does not.
        arrivals = [(n, n // 2) for n in range(40)]   # 2 per step
        service_time = {n: n for (n, _) in arrivals}  # capacity 1, FIFO
        waits = [service_time[n] - arr for (n, arr) in arrivals]
        self.assertTrue(all(w >= 0 for w in waits))
        self.assertEqual(len(service_time), len(arrivals))  # all serviced
        self.assertGreater(waits[-1], waits[len(waits) // 2])
        self.assertEqual(waits[-1], 39 - 19)


class TestOrderSensitivity(unittest.TestCase):
    # 8. a;b services, b;a does not.
    def test_order_matters(self):
        def check(cited, data):
            acts = [r.action for r in cited]
            return "a" in acts and "b" in acts and \
                acts.index("a") < acts.index("b")

        def make(transcript):
            for k in range(len(transcript) + 1):
                cited = tuple(range(k))
                if check(tuple(transcript[i] for i in cited), None):
                    return ServiceCertificate("ordered", cited)
            return None
        spec = ServiceSpec("ordered", check, make)
        self.assertTrue(prover_certified(spec, 
            transcript_of((("a", "."), ("b", ".")))))
        self.assertFalse(prover_certified(spec, 
            transcript_of((("b", "."), ("a", ".")))))
        self.assertFalse(order_irrelevant(
            spec, [(("a", "."), ("b", ".")), (("b", "."), ("a", "."))]))


class TestRepetitionSensitivity(unittest.TestCase):
    # 9. Twice is different from once (replication requirement).
    def test_repetition_matters(self):
        spec_twice = ServiceSpec(
            "replicate",
            lambda cited, data: sum(r.action == "a" for r in cited) >= 2,
            lambda transcript: ServiceCertificate(
                "replicate", tuple(r.index for r in transcript
                                   if r.action == "a"))
            if sum(r.action == "a" for r in transcript) >= 2 else None)
        once = transcript_of((("a", "."),))
        twice = transcript_of((("a", "."), ("a", ".")))
        self.assertFalse(prover_certified(spec_twice, once))
        self.assertTrue(prover_certified(spec_twice, twice))
        self.assertFalse(repetition_irrelevant(
            spec_twice, [(("a", "."),), (("a", "."), ("a", "."))]))


class TestAdversarialResponse(unittest.TestCase):
    # 10. The environment picks among permitted outputs; the controller
    # needs a strategy. Identical to microcase 2's arena but asserted
    # from the game side: the winning object is a policy, and the
    # non-adaptive projections all lose.
    def test_strategy_not_action_set(self):
        def delta(s, a):
            if s == "s0" and a == "ask":
                return {("left", "sL"), ("right", "sR")}
            if s == "sL" and a == "go-left":
                return {("ok", "done")}
            if s == "sR" and a == "go-right":
                return {("ok", "done")}
            return {("na", "dead")}
        env = FiniteStateEnv(("ask", "go-left", "go-right"), "s0", delta)
        mon = Monitor({"i", "acc"}, "i",
                      lambda m, a, y: "acc" if y == "ok" else m, {"acc"})
        self.assertTrue(servable(env, mon))
        # Every static visited-set plan fails on some resolution:
        for n in range(4):
            for seq in itertools.product(env.actions, repeat=n):
                bad = TestResponseDependentBranching.some_run_fails(
                    self, env, mon, seq)
                self.assertTrue(bad)


if __name__ == "__main__":
    unittest.main()
