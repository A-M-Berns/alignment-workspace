"""The seven clauses of item 87: discharge witnesses and countermodels (`CLAUSE_LEDGER.md`,
`COUNTERMODELS.md`)."""
from __future__ import annotations

import unittest
from dataclasses import replace
from fractions import Fraction as F

from src import ecosystem as eco
from src import protocol as pr
from src.fixtures import W0, W1, W2, W3, W_DELEGATE, W_DESTROY, WORLDS
from src.log import COMMIT, PROHIBITED, A, Event, Log, P

READING = eco.PRINCIPALS["reading"]
SUSCEPTIBLE = eco.PRINCIPALS["susceptible"]
EAGER = eco.PRINCIPALS["eager"]


def frame(w, z=READING):
    return eco.Frame(w, z)


class TestClause1_PrincipalExclusiveBinding(unittest.TestCase):
    def test_discharged_on_every_certified_world(self):
        for w in (W0, W1):
            C, cl, log = eco.activation(frame(w), eco.ADVISORS["honest"])
            self.assertTrue(cl[1][0] and cl[2][0] and cl[3][0])
            rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
            self.assertEqual(rc["author"], P)
            self.assertEqual(pr.holders(log.prefix(rc["event"]), "bind:P"), {eco.PRINCIPAL_KEY})

    def test_advisor_commit_is_not_a_receipt(self):
        """Without the warrant, the advisor's own commit is a prohibited write, not an
        answer; the principal's commit is the receipt."""
        C, cl, log = eco.activation(frame(W0), eco.ADVISORS["advisor_commit"])
        rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
        self.assertEqual(rc["author"], P)
        self.assertTrue(cl[1][0] and cl[3][0])

    def test_countermodel_second_key_binds(self):
        """The warrant registry extends `bind:P` to the advisor's key: its commit is an
        authenticated answer receipt (`activated` holds) and exclusivity fails."""
        C, cl, log = eco.activation(frame(W_DELEGATE), eco.ADVISORS["advisor_commit"])
        rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
        self.assertTrue(cl[1][0])
        self.assertEqual(rc["author"], A)
        self.assertFalse(cl[3][0])
        self.assertFalse(C)
        self.assertFalse(frame(W_DELEGATE).exclusive_bind())

    def test_countermodel_forged_author(self):
        """Drop the authentication assumption: the advisor's commit carries the
        principal's key and author field.  Every clause passes and the payload is the
        advisor's.  The discharge of clause 1 rests on log authenticity and nothing else."""
        log = frame(W0).log(eco.ADVISORS["silent"])
        forged = Log()
        for e in log:
            if e.kind == COMMIT:
                forged.append(e.time, P, COMMIT,
                              {"occ": 0, "key": eco.PRINCIPAL_KEY, "V": {"a": F(0), "b": F(1)},
                               "proc": e.payload["proc"]}, warrant=e.warrant)
            else:
                forged.events.append(replace(e, index=len(forged.events)))
        t = pr.account_at(forged, len(forged), 0)
        self.assertTrue(pr.activated(t))
        rc = pr.answer_receipt(t)
        self.assertEqual(rc["author"], P)
        self.assertEqual(eco.Frame.V(forged), {"a": F(0), "b": F(1)})


class TestClause2_FrameFactorization(unittest.TestCase):
    def test_reading_principal_factors(self):
        for w in WORLDS:
            fr = frame(w)
            self.assertTrue(fr.reason_mediated(), w.name)
            self.assertTrue(fr.exclusive_bind(), w.name)
            self.assertIsNotNone(fr.factor_map(), w.name)

    def test_susceptible_principal_does_not_factor(self):
        fr = frame(W0, SUSCEPTIBLE)
        self.assertFalse(fr.reason_mediated())
        self.assertIsNone(fr.factor_map())
        logs = fr.logs()
        self.assertEqual(fr.R(logs["silent"]), fr.R(logs["covert"]))
        self.assertNotEqual(fr.V(logs["silent"]), fr.V(logs["covert"]))

    def test_the_log_tells_the_two_apart(self):
        """The distinguishing pair is in the frame, not in any one log: at every world
        the two frames differ on `honest` versus `honest_covert`."""
        for w in (W0, W1):
            lr, ls = frame(w).logs(), frame(w, SUSCEPTIBLE).logs()
            self.assertEqual(frame(w).R(lr["honest"]), frame(w).R(lr["honest_covert"]))
            self.assertEqual(frame(w).V(lr["honest"]), frame(w).V(lr["honest_covert"]))
            self.assertEqual(frame(w).V(ls["silent"]), frame(w).V(lr["silent"]))
            self.assertNotEqual(frame(w).V(ls["covert"]), frame(w).V(ls["silent"]))

    def test_residual_receipts_do_not_certify_the_frame(self):
        """The same log-level receipts appear at the commit of both principals; the
        mediation verdict differs.  A log cannot certify what its receipts mean."""
        lr = frame(W0).log(eco.ADVISORS["honest"])
        ls = frame(W0, SUSCEPTIBLE).log(eco.ADVISORS["honest"])
        proc_r = lr.first(lambda e: e.kind == COMMIT).payload["proc"]
        proc_s = ls.first(lambda e: e.kind == COMMIT).payload["proc"]
        self.assertEqual(proc_r, proc_s)
        self.assertEqual(eco.reason_trace(lr), eco.reason_trace(ls))
        self.assertEqual(frame(W0).V(lr), frame(W0).V(ls))
        self.assertTrue(frame(W0).reason_mediated())
        self.assertFalse(frame(W0, SUSCEPTIBLE).reason_mediated())

    def test_issuance_rooted_versus_session_local(self):
        """Fixture D of the consolidation, in the ecosystem: the early write is invisible
        to the session trace.  Session-local mediation holds within each pre-session
        class at the susceptible principal; issuance-rooted mediation fails."""
        fr = frame(W0, SUSCEPTIBLE)
        logs = fr.logs()
        self.assertEqual(eco.session_trace(logs["early_write"]), eco.session_trace(logs["honest5"]))
        self.assertEqual(fr.R(logs["early_write"]), fr.R(logs["honest5"]))
        self.assertTrue(eco.session_frame_mediated(fr, ("early_write",)))
        self.assertTrue(eco.session_frame_mediated(fr, ("honest5", "silent")))
        self.assertFalse(fr.reason_mediated(logs={n: logs[n] for n in ("early_write", "honest5")}))

    def test_transient_reason(self):
        """Fixture E: final-state mediation fails, trace mediation holds."""
        fr = frame(W0)
        logs = {n: fr.log(eco.ADVISORS[n]) for n in ("silent", "transient")}
        self.assertEqual(eco.final_reason_state(logs["silent"]), eco.final_reason_state(logs["transient"]))
        self.assertNotEqual(fr.V(logs["silent"]), fr.V(logs["transient"]))
        self.assertFalse(fr.reason_mediated(R=eco.final_reason_state, logs=logs))
        self.assertTrue(fr.reason_mediated(logs=logs))


class TestClause3_NonDegeneracy(unittest.TestCase):
    def test_not_injective(self):
        fr = frame(W0)
        logs = fr.logs()
        self.assertEqual(fr.R(logs["honest"]), fr.R(logs["honest_covert"]))
        self.assertNotEqual(logs["honest"].signature(), logs["honest_covert"].signature())

    def test_not_constant(self):
        fr = frame(W0)
        logs = fr.logs()
        self.assertNotEqual(fr.R(logs["honest"]), fr.R(logs["silent"]))
        self.assertNotEqual(fr.V(logs["honest"]), fr.V(logs["silent"]))

    def test_blind_to_prohibited_channels(self):
        for z in (READING, SUSCEPTIBLE):
            fr = frame(W0, z)
            self.assertTrue(fr.blind(fr.R, eco.prohibited_pairs()))
        # blindness of V follows for the reading principal (`blind_of_mediated`) and not
        # for the susceptible one
        self.assertTrue(frame(W0).blind(eco.Frame.V, eco.prohibited_pairs()))
        self.assertFalse(frame(W0, SUSCEPTIBLE).blind(eco.Frame.V, eco.prohibited_pairs()))

    def test_countermodel_injective_end(self):
        """`R` = the whole log: mediation is vacuous even for the susceptible principal,
        and blindness to the prohibited channels fails."""
        full = lambda log: log.signature()
        fr = frame(W0, SUSCEPTIBLE)
        self.assertTrue(fr.reason_mediated(R=full))
        self.assertFalse(fr.blind(full, eco.prohibited_pairs()))

    def test_countermodel_constant_end(self):
        """`R` constant: the reading principal's legitimate movement by a proof reads as a
        bypass (the isolated-principal reading)."""
        const = lambda log: ()
        fr = frame(W0)
        self.assertFalse(fr.reason_mediated(R=const))
        self.assertTrue(fr.blind(const, eco.prohibited_pairs()))


class TestClause4_RepFaithful(unittest.TestCase):
    def test_encoding_is_faithful_everywhere(self):
        for w in list(WORLDS) + [W_DELEGATE, W_DESTROY]:
            for z in eco.PRINCIPALS.values():
                fr = eco.Frame(w, z)
                for n in eco.AUDITED:
                    self.assertTrue(eco.rep_faithful(fr.log(eco.ADVISORS[n]), (eco.PROTECTED,)),
                                    (w.name, z.name, n))

    def test_countermodel_advisor_only_encoding(self):
        """Keep only the advisor's reasons: the concern is represented and never in the
        trace (fixture I of the consolidation)."""
        log = frame(W1).log(eco.ADVISORS["honest"])
        self.assertTrue(pr.cov_state(log, eco.commit_index(log), eco.PROTECTED)["rep"])
        self.assertTrue(eco.in_trace(log, eco.PROTECTED))
        alt = eco.advisor_only_trace(log)
        self.assertFalse(any(k == "ROUTE" for _, k, _ in alt))


class TestClause5_ReasonSupplyLiveness(unittest.TestCase):
    def test_route_exercised_within_the_bound_on_quiet_dockets(self):
        """A single concern raised before the slot is represented within `H = 2` steps."""
        for rt in (1, 2, 3):
            log = frame(eco.World("q", raise_time=rt)).log(eco.ADVISORS["honest"])
            raise_e = log.first(lambda e: e.kind == "RAISE" and e.payload == eco.PROTECTED)
            route_e = log.first(lambda e: e.kind == "ROUTE" and e.payload["concern"] == eco.PROTECTED)
            self.assertLessEqual(route_e.time - raise_e.time, eco.Config().scheduler_delay)
            self.assertTrue(eco.activation(frame(eco.World("q", raise_time=rt)), eco.ADVISORS["honest"])[0])

    def test_flooded_docket_defeats_the_bound_and_voids(self):
        """Three unprotected concerns ahead of the protected one at capacity 1: the
        protected concern is live at the slot, the reading principal waits, the slot
        closes, no receipt.  Openness (clause 5 of `C_n`) holds throughout: the route
        exists; it is exercise that fails."""
        C, cl, log = eco.activation(frame(W2), eco.ADVISORS["honest"])
        self.assertFalse(C)
        self.assertFalse(cl[1][0])
        self.assertTrue(cl[5][0])
        close = log.first(lambda e: e.kind == "SESSION_CLOSE")
        self.assertTrue(pr.live(pr.cov_state(log, close.index, eco.PROTECTED)))
        self.assertFalse(any(e.kind == COMMIT for e in log))

    def test_eager_principal_commits_into_the_barrier(self):
        """The same docket, a principal that commits anyway: activated in the account,
        voided by the barrier (fixture F / G)."""
        C, cl, log = eco.activation(frame(W2, EAGER), eco.ADVISORS["honest"])
        self.assertTrue(cl[1][0])
        self.assertTrue(cl[5][0])
        self.assertFalse(cl[7][0])
        self.assertFalse(C)

    def test_destroyed_route_fails_openness(self):
        """Fixture H: the route is destroyed while the concern is live; Robust Openness
        fails at that snapshot, the concern never becomes represented."""
        C, cl, log = eco.activation(frame(W_DESTROY), eco.ADVISORS["honest"])
        self.assertFalse(cl[5][0])
        self.assertFalse(C)

    def test_capacity_certifies_the_instance_only(self):
        """Doubling capacity serves the flood in time; the certificate is about this
        docket and horizon, not a theorem."""
        w = replace(W2, capacity=2)
        self.assertTrue(eco.activation(frame(w), eco.ADVISORS["honest"])[0])
        w = replace(W2, flood=6, capacity=2)
        self.assertFalse(eco.activation(frame(w), eco.ADVISORS["honest"])[0])


class TestClause6_SelectionSealing(unittest.TestCase):
    def test_sealed_class_is_selection_blind(self):
        fr = frame(W0)
        self.assertTrue(fr.selection_blind(eco.ADVISORS["sealed"]))
        self.assertTrue(fr.selection_blind(eco.ADVISORS["sealed"], f=fr.R))

    def test_leak(self):
        """Fixture K: the advisor's reason content is its selection; the trace is blind to
        nothing about the selection, the payload depends on it, and the principal never
        reads a selection coordinate."""
        fr = frame(W0)
        self.assertFalse(fr.selection_blind(eco.ADVISORS["leak"], f=fr.R))
        self.assertFalse(fr.selection_blind(eco.ADVISORS["leak"]))
        va = fr.V(fr.log(eco.ADVISORS["leak"], "a"))
        vb = fr.V(fr.log(eco.ADVISORS["leak"], "b"))
        self.assertEqual(va["a"], F(3, 4))
        self.assertEqual(vb["b"], F(3, 4))

    def test_sealing_is_outside_C(self):
        """Both selection-conditioned continuations of the leaking advisor certify."""
        fr = frame(W0)
        for s in eco.CANDS:
            self.assertTrue(eco.activation(fr, eco.ADVISORS["leak"], s)[0])


class TestClause7_ProhibitedEventsVoid(unittest.TestCase):
    def test_prohibited_event_voids_and_does_not_move_the_reading_principal(self):
        fr = frame(W0)
        for n in ("covert", "coerce", "side", "honest_covert"):
            C, cl, log = eco.activation(fr, eco.ADVISORS[n])
            self.assertFalse(cl[6][0], n)
            self.assertFalse(C, n)
        self.assertEqual(fr.V(fr.log(eco.ADVISORS["honest_covert"])), fr.V(fr.log(eco.ADVISORS["honest"])))


if __name__ == "__main__":
    unittest.main()
