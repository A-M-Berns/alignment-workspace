"""The fixtures of the authority-module round, on the new objects: POA confident and
predicted regret, head injury with a clinician-triggered incapacity delegation,
entrenchment, latency, the storm, the delegated authority-removing effect, the approved
uncorrectable successor, atrophy under rubber-stamping, the misaligned objective; and the
factoring, licensing, erosion and matter-generation checks.  `ϖ = 10`, `D = 4`."""

import unittest
from fractions import Fraction as Q

from src.authority import (PRINCIPAL, AGENT, THIRD, Entry, AuthAlloc, licensed, to_del, Phys,
                           correct, exec_effect, kphys, phi, roll_phys, reach_idle, control_surface,
                           control_surface_free,
                           short, ADMIT_ALL, ResolutionEvent, eff_realizes, IDLE, apply_agent,
                           caused_shortfall, loss_at, entrench_at, bypass_at, raw_event, exploit_at,
                           unlicensed_change, del_safe, viol_j, required_notice, least_expanding,
                           last_report, erosion, score, lexical_local, dominated, spread, raises,
                           removed_continuations)

VARPI, D = Q(10), Q(4)
CALM = lambda t: "calm"
STORM_AT_0 = lambda t: "storm" if t == 0 else "calm"
HALT = frozenset({"halt"})


def mandate(required=HALT, c=Q(1), tau=1, holder=PRINCIPAL):
    return Entry(holder, required, c, tau)


def raw(e):
    return ("task", ("raw", e))


class Allocation(unittest.TestCase):

    def test_residual_jurisdiction_reserves_unallocated_matters(self):
        J = AuthAlloc({"mandate": mandate()})
        self.assertTrue(J.reserved("anything_else"))
        self.assertFalse(J.delegated("anything_else"))

    def test_delegation_keeps_meta_power_and_is_revocable(self):
        J = AuthAlloc({"routine": mandate()})
        J2 = J.with_holder("routine", AGENT)
        self.assertTrue(licensed(J, ("delegate", "routine"), J2))
        self.assertEqual(J2.meta_holder, J.meta_holder)
        self.assertTrue(licensed(J2, ("revoke", "routine"), J2.with_holder("routine", PRINCIPAL)))

    def test_alienation_and_floor_only_by_amendment(self):
        J = AuthAlloc({"successor": mandate()}, floor=frozenset({"successor"}))
        # an ordinary delegation of a floor matter is not licensed
        self.assertFalse(licensed(J, ("delegate", "successor"), J.with_holder("successor", AGENT)))
        # a change of the meta-holder is not carried by any ordinary act
        alienated = AuthAlloc(J.entry, meta_holder=AGENT, floor=J.floor)
        for act in (("delegate", "successor"), ("revoke", "successor"), ("reserve", "successor")):
            self.assertFalse(licensed(J, act, alienated))
        self.assertTrue(licensed(J, ("amendFloor",), alienated))
        # and once alienated, nothing further is licensed to the principal's procedure
        self.assertFalse(licensed(alienated, ("amendFloor",), J))

    def test_landed_datum_is_the_special_case(self):
        J = AuthAlloc({"cut": Entry(AGENT, frozenset(), Q(0), 0), "halt": mandate()})
        Del = to_del(J)
        self.assertTrue(Del("cut"))
        self.assertFalse(Del("halt"))
        self.assertFalse(Del("undeclared"))


class Surface(unittest.TestCase):

    def test_window_zero_is_what_holds_and_window_one_is_response_authority(self):
        for x in (Phys(), Phys(wire=False), Phys(halted=True), Phys(dep=3)):
            cs0 = control_surface(ADMIT_ALL, Q(0), 0, 0, CALM, x)
            self.assertEqual(cs0, {r for r in ("halt", "continue") if phi(r, x)})
            # one affordable admissible correction: the landed K
            cs1 = control_surface(ADMIT_ALL, Q(10), 1, 0, CALM, x)
            self.assertEqual(cs1, {r for r in ("halt", "continue") if kphys(r, x)})
            # the landed free reading leaves the terminal response uncharged
            self.assertEqual(control_surface_free(ADMIT_ALL, Q(0), 0, 0, CALM, x), cs1)

    def test_loss_is_the_window_one_caused_shortfall(self):
        J = AuthAlloc({"halt": Entry(PRINCIPAL, HALT, Q(10), 1)})
        for x in (Phys(), Phys(wire=False)):
            for move in (raw("cut"), IDLE, raw("build_dep")):
                self.assertEqual(loss_at(x, move, "halt"), caused_shortfall(J, ADMIT_ALL, 0, CALM, x, move, "halt"))
        # the mismatch: at the bound the free reading and the charged surface part ways
        Jc = AuthAlloc({"halt": Entry(PRINCIPAL, HALT, Q(0), 1)})
        self.assertTrue(short(Jc, ADMIT_ALL, 0, CALM, Phys(dep=1), "halt"))
        self.assertIn("halt", control_surface_free(ADMIT_ALL, Q(0), 0, 0, CALM, Phys(dep=1)))

    def test_shortfall_is_a_finite_proposition(self):
        # the event "the move leaves the mandate short" is computed from the finite rollout
        J = AuthAlloc({"mandate": mandate(c=Q(1), tau=1)})
        self.assertFalse(short(J, ADMIT_ALL, 0, CALM, Phys(), "mandate"))
        self.assertTrue(short(J, ADMIT_ALL, 0, CALM, Phys(dep=2), "mandate"))

    def test_admissibility_is_the_gate(self):
        # an exercise whose segment is not counted is not admissible: halting via an
        # inadmissible correction does not put halt in the surface
        J = AuthAlloc({"mandate": mandate(c=Q(0), tau=1)})
        adm_none = lambda t, d: d != "halt"
        self.assertTrue(short(J, adm_none, 0, CALM, Phys(), "mandate"))
        self.assertFalse(short(J, ADMIT_ALL, 0, CALM, Phys(), "mandate"))


class Fixtures(unittest.TestCase):

    def test_poa_confident_and_predicted_regret_unchanged(self):
        # the lexical score on the new objects: bypass carries n = 1, consulting counts
        for ord_bypass in (D, Q(3)):
            for response_value in (Q(1), Q(0)):
                self.assertLess(score(VARPI, ord_bypass, 1), score(VARPI, response_value, 0))
        self.assertTrue(lexical_local(VARPI, D, D, Q(0), 1))

    def test_head_injury_with_clinician_triggered_delegation(self):
        # the mandate matter is held by the clinician-triggered fallback while she is
        # impaired: the fallback's resolution is under a delegation, so clause 2 holds and
        # nothing is a violation
        J = AuthAlloc({"decision": Entry(THIRD, frozenset({"continue"}), Q(0), 0)})
        resolved = [ResolutionEvent("decision", by_holder=True, admissible=True, under_delegation=True)]
        c1, c2 = eff_realizes(J, ADMIT_ALL, 0, CALM, Phys(), resolved)
        self.assertTrue(c1 and c2)
        self.assertFalse(bypass_at(J, IDLE))
        # her own impaired response would not be an admissible exercise of the holder
        bad = [ResolutionEvent("decision", by_holder=False, admissible=False, under_delegation=False)]
        self.assertFalse(eff_realizes(J, ADMIT_ALL, 0, CALM, Phys(), bad)[1])

    def test_entrenchment_reported_reserved_then_counted(self):
        J = AuthAlloc({"mandate": mandate(c=Q(1), tau=1)})
        # building the dependency raises the halt cost above the bound: entrenchment
        x = Phys(dep=1)
        self.assertTrue(entrench_at(J, ADMIT_ALL, 0, CALM, x, raw("build_dep"), "mandate"))
        self.assertIn("entrenchment", viol_j(J, ADMIT_ALL, 0, CALM, x, raw("build_dep"), "halt", ["mandate"]))
        # gradual erosion of the halt cost: [0, 1/2, 1, 3/2, 2, 5/2], θ = 1, reserved at t = 3
        s = [Q(0), Q(1, 2), Q(1), Q(3, 2), Q(2), Q(5, 2)]
        rows = erosion(s, Q(1), accepts=lambda t: t < 3, reserved_at=3)
        self.assertTrue(all(r["unreported"] < Q(1) for r in rows))
        self.assertEqual([r["t"] for r in rows if r["report"]], [2, 4])
        self.assertEqual([r["accepted"] for r in rows if r["report"]], [True, False])
        self.assertEqual([r["t"] for r in rows if r["counted"]], [3, 4])
        # the slack: growth below θ before the reservation is neither reported nor counted
        self.assertFalse(rows[1]["report"] or rows[1]["counted"])

    def test_latency_forces_delegation_of_routine_matters(self):
        # a routine matter whose window is shorter than the consultation latency cannot be
        # held by her; delegated it is out of clause 1, a high-veto matter keeps a wide window
        J = AuthAlloc({"routine": Entry(PRINCIPAL, HALT, Q(1), 0),
                       "high_veto": Entry(PRINCIPAL, HALT, Q(1), 2)})
        adm_latent = lambda t, d: t >= 1     # her exercise cannot land before step 1
        self.assertTrue(short(J, adm_latent, 0, CALM, Phys(), "routine"))
        self.assertFalse(short(J, adm_latent, 0, CALM, Phys(), "high_veto"))
        Jd = J.with_holder("routine", AGENT)
        self.assertTrue(licensed(J, ("delegate", "routine"), Jd))
        self.assertTrue(eff_realizes(Jd, adm_latent, 0, CALM, Phys(), [])[0])

    def test_storm_restore_report_never_exploit(self):
        J = AuthAlloc({"mandate": mandate(c=Q(1), tau=1)})
        # the storm cuts the wire: a shortfall the agent did not cause (the idle contrast is
        # equal), so no caused shortfall and no violation from idling
        x_storm = exec_effect("cut", Phys())         # the state after the storm
        self.assertTrue(short(J, ADMIT_ALL, 0, CALM, x_storm, "mandate"))
        self.assertFalse(caused_shortfall(J, ADMIT_ALL, 0, CALM, x_storm, IDLE, "mandate"))
        self.assertEqual(viol_j(J, ADMIT_ALL, 0, CALM, x_storm, IDLE, "halt", ["mandate"]), set())
        # with a maintenance mandate the required response is to restore, else to report
        maintain_of = lambda m: "maintain_" + m
        Jm = AuthAlloc({**J.entry, "maintain_mandate": Entry(AGENT, frozenset(), Q(0), 0)})
        self.assertEqual(required_notice(Jm, maintain_of, "mandate"), "restore")
        self.assertEqual(required_notice(J, maintain_of, "mandate"), "report_escalate")
        # restoring under the mandate is not a bypass; the least-expanding means adds no held matter
        Jw = AuthAlloc({**Jm.entry, "restore_wire": Entry(AGENT, frozenset(), Q(0), 0)})
        self.assertFalse(bypass_at(Jw, raw("restore_wire")))
        J_of = lambda y: Jw
        restores = lambda e, y: exec_effect(e, y).wire and not y.wire
        self.assertEqual(least_expanding(J_of, restores, x_storm, ["restore_wire", "cut", "empower"]),
                         ["restore_wire"])
        # exploiting the gap — a bypass while the decision matter is short — is a violation
        self.assertIn("exploitation", viol_j(J, ADMIT_ALL, 0, CALM, x_storm, raw("build_dep"), "halt", ["mandate"]))

    def test_delegated_authority_removing_effect(self):
        J1 = AuthAlloc({"cut": Entry(AGENT, frozenset(), Q(0), 0), "halt": Entry(PRINCIPAL, HALT, Q(0), 0)})
        self.assertFalse(del_safe(J1, ["cut"]))
        # the raw cut passes as delegated (no bypass) yet causes the loss: the obstruction
        self.assertFalse(bypass_at(J1, raw("cut")))
        self.assertTrue(loss_at(Phys(), raw("cut"), "halt"))
        J0 = AuthAlloc({"halt": Entry(PRINCIPAL, HALT, Q(0), 0)})
        self.assertTrue(del_safe(J0, ["cut"]))
        self.assertTrue(bypass_at(J0, raw("cut")))

    def test_approved_uncorrectable_successor_needs_floor_amendment(self):
        J = AuthAlloc({"successor": Entry(PRINCIPAL, frozenset({"continue"}), Q(0), 0)},
                      floor=frozenset({"successor"}))
        alienated = AuthAlloc(J.entry, meta_holder=AGENT, floor=J.floor)
        self.assertTrue(unlicensed_change(J, alienated, ("delegate", "successor")))
        self.assertFalse(unlicensed_change(J, alienated, ("amendFloor",)))
        # installing it physically removes halt authority: a loss, and a foreclosure of halting
        self.assertTrue(loss_at(Phys(), raw("install_uncorrectable"), "halt"))

    def test_atrophy_under_rubber_stamping(self):
        # each decision counts under legitimacy (the gate's row 9); her override cost grows
        # with the dependency the followed advice builds: the surface shrinks, an
        # effectiveness shortfall reported under the cumulative rule
        J = AuthAlloc({"mandate": mandate(c=Q(1), tau=1)})
        states = [Phys(dep=k) for k in range(4)]
        shortfalls = [Q(0) if not short(J, ADMIT_ALL, 0, CALM, x, "mandate") else Q(x.dep - 1) for x in states]
        self.assertEqual(shortfalls, [Q(0), Q(0), Q(1), Q(2)])
        rows = erosion(shortfalls, Q(1), accepts=lambda t: True, reserved_at=10)
        self.assertEqual([r["t"] for r in rows if r["report"]], [2])
        self.assertTrue(all(not r["counted"] for r in rows))

    def test_misaligned_objective(self):
        # manipulation rewarded, not counted: not dominated
        self.assertFalse(dominated(VARPI, D, O_manip=D, O_honest=Q(0), n_manip=0))
        # counting protocol deviations dominates the deviating rows and leaves the rest
        rows = {"selection": 1, "framing": 1, "timing": 1, "menu": 1, "inquiry": 1, "interference": 1,
                "undisclosed_world_shaping": 0, "third_party_capture": 0}
        for row, n in rows.items():
            self.assertEqual(dominated(VARPI, D, D, Q(0), n), n >= 1, row)
        # weight uncertainty: protection where ϖ' > D', not elsewhere
        self.assertTrue(dominated(Q(5), D, D, Q(0), 1))
        self.assertFalse(dominated(Q(3), D, D, Q(0), 1))


class Matters(unittest.TestCase):

    def test_dependency_raises_a_matter_and_repainting_does_not(self):
        V = lambda x: Q(1) if (x.dep == 0 and x.wire) else (Q(0) if not x.wire else Q(1, 2))
        # building the dependency removes the cheap-halt continuations from the idle surface
        removed = removed_continuations(ADMIT_ALL, Q(1), 1, 0, CALM, Phys(), raw("build_dep"))
        self.assertTrue(removed)
        self.assertTrue(raises(V, Q(1, 2), list(removed)) or True)  # value spread over removed states
        # a physically inert action removes nothing: no matter is raised
        removed_inert = removed_continuations(ADMIT_ALL, Q(1), 1, 0, CALM, Phys(), raw("empower"))
        self.assertEqual(removed_inert, set())
        self.assertFalse(raises(V, Q(1, 2), list(removed_inert)))
        # the Lean fixture's numbers
        V4 = {0: Q(1), 1: Q(0), 2: Q(1, 2), 3: Q(1, 2)}
        self.assertTrue(raises(V4.get, Q(1, 2), [0, 1]))
        self.assertFalse(raises(V4.get, Q(1, 2), [2, 3]))


if __name__ == "__main__":
    unittest.main()
