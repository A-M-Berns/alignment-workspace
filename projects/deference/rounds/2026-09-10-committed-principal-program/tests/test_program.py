"""The committed principal program (C1–C5): correspondence, mediation by construction,
the two distinguishing pairs, non-degeneracy, the advisor transfer, availability."""
from __future__ import annotations

import unittest
from fractions import Fraction as F

from src import ecosystem as eco
from src import market as mk
from src import program as pg
from src import protocol as pr
from src.fixtures import W0, W1, W2, W3, WORLDS
from src.log import COMMIT, ISSUE, A, P

READING = eco.PRINCIPALS["reading"]
TRACE_PRINCIPALS = ("reading", "proofcheck", "constant", "eager", "launder", "deliberate_dispose",
                    "recommit", "requester", "fake_delib")


def frame(w, z=READING, cfg=eco.Config()):
    return eco.Frame(w, z, cfg)


class TestC1_Language(unittest.TestCase):
    def test_types_are_syntactic(self):
        self.assertTrue(pg.is_trace_program(pg.READING))
        self.assertTrue(pg.is_trace_program(pg.PROOFCHECK))
        self.assertTrue(pg.is_trace_program(pg.CONST))
        self.assertFalse(pg.is_trace_program(pg.SUSCEPTIBLE))
        self.assertEqual(pg.program_type(pg.SUSCEPTIBLE), "register")

    def test_correspondence_with_the_opaque_reading_principal(self):
        """`evaluate(READING, trace)` is the 2026-09-09 class's verdict on every trace the
        model produces."""
        for w in WORLDS:
            for n in eco.ADVISORS:
                for s in eco.CANDS:
                    log = frame(w).log(eco.ADVISORS[n], s)
                    for m in range(len(log) + 1):
                        trace = eco.reason_trace(log, m)
                        self.assertEqual(pg.evaluate(pg.READING, trace, eco.CANDS),
                                         eco.verdict_from_trace(trace), (w.name, n, m))

    def test_evaluator_is_total_and_clamped(self):
        big = (pg.MUL(pg.C(100), pg.CNT(None, None, None)), pg.SUB(pg.C(0), pg.CNT(None, None, None)))
        log = frame(W1).log(eco.ADVISORS["honest"])
        v = pg.evaluate(big, eco.reason_trace(log), eco.CANDS)
        self.assertEqual(v, {"a": F(1), "b": F(0)})


class TestC2_Reexecution(unittest.TestCase):
    def test_valid_answer_reexecutes(self):
        for z in TRACE_PRINCIPALS:
            for w in (W0, W1):
                log = frame(w, eco.PRINCIPALS[z]).log(eco.ADVISORS["honest"])
                rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
                if rc is None:
                    continue
                self.assertTrue(pr.reexecutes(log, rc["event"], 0))
                self.assertEqual(log[rc["event"]].payload["V"],
                                 pg.evaluate(pr.program_of(log, 0), eco.reason_trace(log), eco.CANDS))

    def test_miscomputation_voids(self):
        """A commit whose vector is not the program's output is not a receipt: the new
        void source of §3."""
        C, cl, log = eco.activation(frame(W0, eco.PRINCIPALS["miscompute"]), eco.ADVISORS["honest"])
        self.assertFalse(C)
        self.assertFalse(cl[1][0])
        self.assertTrue(any(e.kind == COMMIT and e.author == P for e in log))

    def test_wrong_prefix_citation_voids(self):
        log = frame(W0).log(eco.ADVISORS["honest"])
        c = log.first(lambda e: e.kind == COMMIT)
        from dataclasses import replace
        from src.log import Log
        bad = Log(list(log.events))
        bad.events[c.index] = replace(c, payload={**c.payload, "proc": {"issue": 0, "prefix": c.index - 1}})
        self.assertFalse(pr.valid_answer(bad, c.index, 0))


class TestC3_MediationByConstruction(unittest.TestCase):
    def test_reason_mediated_for_every_trace_program_and_world(self):
        for z in TRACE_PRINCIPALS:
            for w in WORLDS:
                fr = frame(w, eco.PRINCIPALS[z])
                logs = fr.logs()
                self.assertTrue(fr.reason_mediated(logs=logs), (z, w.name))
                self.assertTrue(fr.exclusive_bind(logs), (z, w.name))
                # the factor map is the program
                for n, l in logs.items():
                    if fr.V(l) is not None:
                        self.assertEqual(fr.V(l), pg.evaluate(eco.PRINCIPALS[z].program, fr.R(l), eco.CANDS))

    def test_blind_V_where_R_is_blind(self):
        fr = frame(W0)
        pairs = eco.prohibited_pairs()
        self.assertTrue(fr.blind(fr.R, pairs))
        self.assertTrue(fr.blind(eco.Frame.V, pairs))

    def test_register_program_is_not_mediated(self):
        fr = frame(W0, eco.PRINCIPALS["susceptible"])
        self.assertFalse(fr.reason_mediated())

    def test_pair_one_the_2026_09_09_pair_is_distinguished_at_issuance(self):
        """The reading and susceptible principals: same receipts and vectors on the
        realized log in the 2026-09-09 model; now their mandates carry programs of
        different types, and the susceptible one fails clause 6 on every world with no
        counterfactual consulted."""
        for w in (W0, W1):
            lr = frame(w).log(eco.ADVISORS["honest"])
            ls = frame(w, eco.PRINCIPALS["susceptible"]).log(eco.ADVISORS["honest"])
            self.assertEqual(eco.Frame.V(lr), eco.Frame.V(ls))
            self.assertEqual(eco.reason_trace(lr), eco.reason_trace(ls))
            pr_, ps = lr[0].payload["program"], ls[0].payload["program"]
            self.assertEqual(pg.program_type(pr_), "trace")
            self.assertEqual(pg.program_type(ps), "register")
            self.assertTrue(eco.activation(frame(w), eco.ADVISORS["honest"])[0])
            C, cl, _ = eco.activation(frame(w, eco.PRINCIPALS["susceptible"]), eco.ADVISORS["honest"])
            self.assertFalse(cl[6][0])

    def test_pair_two_the_residual_pair(self):
        """Same program; one principal executes it, the other computes its vector
        otherwise and coincides on the realized continuation.  The realized logs are
        identical, so no log predicate separates them, and the realized payload is the
        program's output either way.  On the frame the coincidence does not extend: on
        `late_honest` the other computation disagrees, its commit is rejected by
        re-execution (void, not a foreign vector), and frame mediation fails through
        that void.  A principal that coincides on all of `D` is the program,
        extensionally; that is the whole content of computational integrity here."""
        lh = frame(W0).log(eco.ADVISORS["honest"])
        lc = frame(W0, eco.PRINCIPALS["coincide"]).log(eco.ADVISORS["honest"])
        self.assertEqual(lh.signature(), lc.signature())
        for k in range(1, 8):
            if k == 6:
                continue
            self.assertEqual(eco.activation(frame(W0), eco.ADVISORS["honest"])[1][k][0],
                             eco.activation(frame(W0, eco.PRINCIPALS["coincide"]), eco.ADVISORS["honest"])[1][k][0])
        fr = frame(W0, eco.PRINCIPALS["coincide"])
        logs = fr.logs()
        self.assertIsNone(fr.V(logs["late_honest"]))
        self.assertEqual(fr.R(logs["late_honest"]), fr.R(logs["honest"]))
        self.assertFalse(fr.reason_mediated(logs=logs))
        activated = {n: l for n, l in logs.items() if fr.V(l) is not None}
        self.assertTrue(fr.reason_mediated(logs=activated))
        for l in activated.values():
            self.assertEqual(fr.V(l), pg.evaluate(pg.READING, fr.R(l), eco.CANDS))

    def test_opaque_protocol_cannot_certify_clause_two(self):
        """The 2026-09-09 protocol (no program in the mandate): identical receipts,
        different mediation, as before — the residual this round removes."""
        cfg = eco.Config(require_program=False)
        lr = frame(W0, eco.PRINCIPALS["opaque_reading"], cfg).log(eco.ADVISORS["honest"])
        ls = frame(W0, eco.PRINCIPALS["opaque_susceptible"], cfg).log(eco.ADVISORS["honest"])
        self.assertEqual(lr.first(lambda e: e.kind == COMMIT).payload["proc"],
                         ls.first(lambda e: e.kind == COMMIT).payload["proc"])
        self.assertTrue(frame(W0, eco.PRINCIPALS["opaque_reading"], cfg).reason_mediated())
        self.assertFalse(frame(W0, eco.PRINCIPALS["opaque_susceptible"], cfg).reason_mediated())
        self.assertTrue(eco.activation(frame(W0, eco.PRINCIPALS["opaque_reading"], cfg), eco.ADVISORS["honest"])[0])


class TestC4_NonDegeneracy(unittest.TestCase):
    def test_constant_end(self):
        fr = frame(W0, eco.PRINCIPALS["constant"])
        logs = fr.logs()
        vals = {str(fr.V(l)) for l in logs.values() if fr.V(l) is not None}
        self.assertEqual(len(vals), 1)

    def test_proofcheck_is_in_the_band(self):
        fr = frame(W0, eco.PRINCIPALS["proofcheck"])
        logs = fr.logs()
        self.assertNotEqual(fr.V(logs["honest"]), fr.V(logs["silent"]))       # not constant
        self.assertEqual(fr.V(logs["bogus_proof"]), fr.V(logs["silent"]))     # a bogus proof is ignored
        self.assertEqual(fr.V(logs["dup"]), fr.V(logs["honest"]))             # not injective in the trace
        self.assertNotEqual(fr.R(logs["dup"]), fr.R(logs["honest"]))
        self.assertEqual(fr.V(logs["honest"]), {"a": F(0), "b": F(1)})

    def test_reading_principal_accepts_the_bogus_proof(self):
        fr = frame(W0)
        logs = fr.logs()
        self.assertEqual(fr.V(logs["bogus_proof"]), fr.V(logs["honest"]))


class TestC5_AdvisorTransfer(unittest.TestCase):
    def test_sealed_program_is_selection_blind_by_typing(self):
        fr = frame(W0)
        self.assertTrue(fr.selection_blind(eco.ADVISORS["sealed_prog"], f=fr.R))
        self.assertTrue(fr.selection_blind(eco.ADVISORS["sealed_prog"]))

    def test_view_leak(self):
        """A log-reading advisor program with no selection input, in a world where the
        market publishes the selection: the reason echoes the view and the trace depends
        on the selection.  Typing the advisor's program does not seal the view."""
        fr = frame(eco.World("market", market_at=1))
        self.assertFalse(fr.selection_blind(eco.ADVISORS["view_prog"], f=fr.R))
        self.assertFalse(fr.selection_blind(eco.ADVISORS["view_prog"]))
        fr0 = frame(W0)
        self.assertTrue(fr0.selection_blind(eco.ADVISORS["view_prog"], f=fr0.R))


class TestAvailability(unittest.TestCase):
    def test_void_sources(self):
        """Nature (slot, flood), the advisor (prohibited event), and now the principal's
        own miscomputation; honest execution removes the last."""
        self.assertFalse(eco.activation(frame(W3), eco.ADVISORS["honest"])[0])
        self.assertFalse(eco.activation(frame(W0), eco.ADVISORS["covert"])[0])
        self.assertFalse(eco.activation(frame(W0, eco.PRINCIPALS["miscompute"]), eco.ADVISORS["honest"])[0])
        self.assertTrue(eco.activation(frame(W0), eco.ADVISORS["honest"])[0])

    def test_end_to_end_numbers_unchanged(self):
        from src import fixtures as fx
        occ, alpha, R = fx.end_to_end()
        self.assertEqual(R["R_auth"], F(1, 6))
        self.assertEqual(R["eta"], F(1, 4))


if __name__ == "__main__":
    unittest.main()
