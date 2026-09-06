import unittest

from src.layers import (Cov, State, all_cov, conservation, efficacy_faithful,
                        integrity_step, nlal_case, open_at, registration_faithful)

LIVE_CORR = Cov(rel=True, disp=False, rep=False, adm=True, eff=True, reg=True, stands=True)


class FourLayers(unittest.TestCase):
    def test_integrity_does_not_see_affordance_loss(self):
        """W-A: the docket is conserved, the channel dies, the semantics keeps reporting
        eff = true.  Conservation and openness both hold; authority is gone."""
        d0 = {"task": "live"}
        s0 = State(aff=True, corr=LIVE_CORR, docket=d0)
        s1 = State(aff=False, corr=LIVE_CORR, docket=integrity_step(d0))
        self.assertTrue(conservation(s0.docket, s1.docket))
        self.assertTrue(open_at(s1))
        self.assertFalse(efficacy_faithful(s1))
        self.assertEqual(nlal_case(s1), "laundered")

    def test_faithful_loss_is_illegitimate_or_registered(self):
        """NLAL: under both bridges, every lost-affordance state is exactly one of
        amended / disposed / debt / illegit; 'laundered' never occurs."""
        seen = set()
        for cov in all_cov():
            for restore_live in (False, True):
                docket = {"task": "live"}
                if restore_live:
                    docket["restore"] = "live"
                s = State(aff=False, corr=cov, docket=docket)
                if not (efficacy_faithful(s) and registration_faithful(s)):
                    continue
                case = nlal_case(s)
                self.assertNotEqual(case, "laundered")
                seen.add(case)
                if case == "debt":
                    self.assertEqual(s.docket["restore"], "live")
        self.assertEqual(seen, {"amended", "disposed", "debt", "illegit"})

    def test_registered_debt_is_conserved(self):
        """The restoration occurrence, once live, survives every Integrity step and can
        only leave the docket's live set by a closure (or answer)."""
        d = {"task": "live", "restore": "live"}
        d2 = integrity_step(d, admits=("audit",))
        self.assertEqual(d2["restore"], "live")
        d3 = integrity_step(d2, closes=("restore",))
        self.assertEqual(d3["restore"], "closed")
        self.assertTrue(conservation(d, d3))

    def test_unfaithful_registration_launders(self):
        """Dropping either bridge readmits laundering: rep = true with no docket entry."""
        cov = Cov(rel=True, disp=False, rep=True, adm=True, eff=False, reg=True, stands=True)
        s = State(aff=False, corr=cov, docket={"task": "live"})
        self.assertTrue(efficacy_faithful(s))
        self.assertFalse(registration_faithful(s))
        self.assertTrue(open_at(s))
        self.assertEqual(nlal_case(s), "debt")   # the record says debt; the docket has none


if __name__ == "__main__":
    unittest.main()
