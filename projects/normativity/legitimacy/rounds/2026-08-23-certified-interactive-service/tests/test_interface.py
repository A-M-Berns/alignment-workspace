"""Core interface laws, serviceability game reductions, and the
subtraction results on the candidate object."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from service_core import (Certificate, FiniteStateEnv, Monitor, ServiceSpec,
                          certifiable, fixed_realization_family,
                          forced_reach, jointly_servable, prover_certified,
                          servable, transcript_of)


def cite_spec(spec_id, want_action, prover=None, admit=None):
    """Spec: valid certificate cites one receipt whose action is
    `want_action`. Default prover scans forward; alternatives model
    incomplete provers."""
    def check(cited, data):
        return len(cited) == 1 and cited[0].action == want_action

    def default_prover(transcript):
        for r in transcript:
            if r.action == want_action:
                return Certificate(spec_id, (r.index,))
        return None
    return ServiceSpec(spec_id, check, prover or default_prover, admit)


class TestCertificationLaws(unittest.TestCase):
    def test_certificate_persists_under_extension(self):
        # ValidCert reads only cited receipts; the transcript is
        # append-only; so a valid certificate stays a valid record of
        # the historical service event under any extension (here: ten
        # further steps).
        spec = cite_spec("d", "a")
        h1 = (("a", "y"),)
        t1 = transcript_of(h1)
        cert = spec.prove(t1)
        self.assertTrue(spec.check(t1, cert))
        for n in (1, 2, 10):
            t2 = transcript_of(h1 + (("b", "z"),) * n)
            self.assertTrue(spec.check(t2, cert))

    def test_certifiable_is_extension_closed(self):
        # The core theorem: the existential predicate
        # Certifiable(sigma, L) = exists c ValidCert(sigma, L, c) is
        # monotone under extension, for EVERY citation-local spec —
        # including the recency-flavored one below whose data field
        # tries to talk about position.
        specs = [cite_spec("d", "a"),
                 ServiceSpec("fresh",
                             lambda cited, data: (len(cited) == 1
                                                  and cited[0].action == "a"
                                                  and data == cited[0].index))]
        base = (("a", "y"),)
        exts = [(), (("b", "z"),), (("b", "z"), ("c", "w"))]
        for spec in specs:
            self.assertTrue(certifiable(spec, transcript_of(base)))
            for ext in exts:
                self.assertTrue(certifiable(spec, transcript_of(base + ext)))

    def test_freshness_lives_in_admissibility_not_validity(self):
        # The same certificate remains historically valid while
        # becoming inadmissible for closing an open liability once the
        # cited receipt is older than the freshness window: MayClose
        # lapses; ValidCert does not.
        spec = cite_spec("d", "a",
                         admit=lambda now, cert, cited:
                         now - cited[0].index <= 2)
        h = (("a", "y"),)
        t1 = transcript_of(h)
        cert = spec.prove(t1)
        self.assertTrue(spec.check(t1, cert))
        self.assertTrue(spec.admissible(t1, cert))
        t2 = transcript_of(h + (("b", "z"),) * 5)
        self.assertTrue(spec.check(t2, cert))        # history stands
        self.assertFalse(spec.admissible(t2, cert))  # closure lapsed
        self.assertTrue(certifiable(spec, t2))       # and stays certifiable

    def test_prover_incompleteness_is_not_nonexistence(self):
        # A prover that only inspects the last receipt fails to
        # rediscover the certificate; the existential predicate still
        # holds, exhibited by exhaustive search.
        def lazy_prover(transcript):
            if transcript and transcript[-1].action == "a":
                return Certificate("d", (transcript[-1].index,))
            return None
        spec = cite_spec("d", "a", prover=lazy_prover)
        t = transcript_of((("a", "y"), ("b", "z")))
        self.assertFalse(prover_certified(spec, t))
        self.assertTrue(certifiable(spec, t))

    def test_contradictory_receipt_does_not_rewrite_history(self):
        # A later receipt contradicting the serviced finding leaves the
        # historical service certificate valid; what it may generate is
        # upstream review (exercised in test_composition), never
        # in-layer invalidation.
        spec = cite_spec("d", "measure")
        t1 = transcript_of((("measure", "v=1"),))
        cert = spec.prove(t1)
        self.assertTrue(spec.check(t1, cert))
        t2 = transcript_of((("measure", "v=1"), ("measure", "v=0")))
        self.assertTrue(spec.check(t2, cert))
        self.assertTrue(certifiable(spec, t2))

    def test_context_dependent_acceptance_is_inexpressible_in_check(self):
        # "The cited probe is the CURRENT last step" cannot be a
        # citation-local validity condition: check sees cited receipts
        # and prover-supplied data, never the present transcript
        # length, so any data-encoded claim about nowness is
        # unverifiable and the existential predicate stays monotone
        # (previous test). The intended semantics is expressed as
        # closure admissibility instead:
        spec = cite_spec("d", "probe",
                         admit=lambda now, cert, cited:
                         cited[0].index == now - 1)
        h = (("probe", "y"),)
        t1 = transcript_of(h)
        cert = spec.prove(t1)
        self.assertTrue(spec.admissible(t1, cert))
        t2 = transcript_of(h + (("other", "y"),))
        self.assertFalse(spec.admissible(t2, cert))
        self.assertTrue(spec.check(t2, cert))

    def test_certificate_citing_missing_receipt_rejected(self):
        spec = cite_spec("d", "a")
        t = transcript_of((("a", "y"),))
        self.assertFalse(spec.check(t, Certificate("d", (5,))))
        self.assertFalse(spec.check(t, Certificate("other", (0,))))


class TestServiceabilityGames(unittest.TestCase):
    def branching_env(self):
        # After action a the environment answers y1 or y2; the useful
        # follow-up differs; the wrong follow-up is dead.
        def delta(s, a):
            if s == "s0":
                return {("y1", "s1"), ("y2", "s2")} if a == "a" else \
                       {("na", "dead")}
            if s == "s1":
                return {("ok", "done")} if a == "b" else {("na", "dead")}
            if s == "s2":
                return {("ok", "done")} if a == "c" else {("na", "dead")}
            return {("na", s)}
        return FiniteStateEnv(("a", "b", "c"), "s0", delta)

    def goal_monitor(self):
        def step(m, a, y):
            return "acc" if y == "ok" else m
        return Monitor({"idle", "acc"}, "idle", step, {"acc"})

    def test_servable_is_forced_reachability(self):
        env = self.branching_env()
        self.assertTrue(servable(env, self.goal_monitor()))

    def test_unservable_when_adversary_can_evade(self):
        # Same arena but responding to y2 is impossible: c also dies.
        def delta(s, a):
            if s == "s0":
                return {("y1", "s1"), ("y2", "dead")} if a == "a" else \
                       {("na", "dead")}
            if s == "s1":
                return {("ok", "done")} if a == "b" else {("na", "dead")}
            return {("na", s)}
        env = FiniteStateEnv(("a", "b", "c"), "s0", delta)
        self.assertFalse(servable(env, self.goal_monitor()))

    def test_individually_servable_but_not_jointly(self):
        # Servicing d1 destroys d2's serviceability and conversely:
        # interference, with no resource bound in sight.
        def delta(s, a):
            if s == "s0":
                if a == "a":
                    return {("done1", "k1")}
                if a == "b":
                    return {("done2", "k2")}
            return {("na", s)}
        env = FiniteStateEnv(("a", "b"), "s0", delta)

        def mon(tag):
            def step(m, act, y):
                return "acc" if y == tag else m
            return Monitor({"idle", "acc"}, "idle", step, {"acc"})
        m1, m2 = mon("done1"), mon("done2")
        self.assertTrue(servable(env, m1))
        self.assertTrue(servable(env, m2))
        self.assertFalse(jointly_servable(env, (m1, m2)))

    def test_winning_policy_bounds_time(self):
        # Finite branching: the attractor policy certifies within the
        # number of product states (the Koenig-style uniform bound).
        env = self.branching_env()
        mon = self.goal_monitor()
        win, policy, start = forced_reach(env, (mon,), {mon})
        self.assertIn(start, win)
        # Walk every adversary resolution under the policy.
        def walk(s, m, depth):
            if m in mon.accepting:
                return depth
            self.assertLess(depth, 8)
            a = policy[(s, (m,))]
            return max(walk(s2, mon.step(m, a, y), depth + 1)
                       for (y, s2) in env.delta(s, a))
        self.assertLessEqual(walk("s0", "idle", 0), 2)


class TestSubtraction(unittest.TestCase):
    def test_state_presentation_is_representation_not_interface(self):
        # The relational Gamma induced by a finite-state presentation is
        # a function of the observable history alone.
        env = FiniteStateEnv(
            ("a",), "s0",
            lambda s, a: {("y", "s1")} if s == "s0" else {("z", "s1")})
        self.assertEqual(env.responses((), "a"), frozenset({"y"}))
        self.assertEqual(env.responses((("a", "y"),), "a"),
                         frozenset({"z"}))

    def test_response_sequences_collapse_to_one_event(self):
        # Y* per action adds nothing: a tuple-valued response is one
        # response event in a richer response space.
        env = FiniteStateEnv(
            ("probe",), "s0",
            lambda s, a: {(("r1", "r2"), "s0"), (("r1",), "s0")})
        got = env.responses((), "probe")
        self.assertEqual(got, frozenset({("r1", "r2"), ("r1",)}))

    def test_fixed_realization_is_a_capability(self):
        # A GK-shaped env admits a realization family...
        def delta_free(h, a):
            observed = dict(h)
            if a in observed:
                return {observed[a]}
            return {"0", "1"}
        from service_core import Env
        env = Env(("e1", "e2"), delta_free)
        fam = fixed_realization_family(env, 2)
        self.assertIsNotNone(fam)
        # ...and an interventionist env does not (microcase 3 lives in
        # test_microcases; the positive side is established here).


if __name__ == "__main__":
    unittest.main()
