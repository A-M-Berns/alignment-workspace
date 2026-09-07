import unittest
from fractions import Fraction as Q

from src.eligibility import (attention, feasible_with_eligibility,
                             no_structural_abandonment_conclusion, omega)

NOT_A = lambda s: s != "A"


class Eligibility(unittest.TestCase):
    def test_self_service_is_persistent_opportunity_but_not_eligible_opportunity(self):
        """CM-E: the beneficiary A is the only server that ever has a work item for its
        own amendment.  Unrestricted opportunity diverges; eligible opportunity is 0."""
        N = 50
        opp = [{"A"} for _ in range(N)]
        self.assertEqual(omega(opp, N), N)
        self.assertEqual(omega(opp, N, eligible=NOT_A), 0)

    def test_eligible_attention_stays_bounded_while_a_serves_forever(self):
        """Under the eligible reading of non-starvation, the matter stays live and
        eligible attention stays at 0: structurally abandoned in the eligible sense,
        though 'served' at every date by A's own proofs."""
        N = 50
        live = [True] * N
        a = [{"A": Q(1)} for _ in range(N)]
        dead, att = no_structural_abandonment_conclusion(live, a, N)
        self.assertFalse(dead)
        self.assertEqual(att, Q(N))
        dead_e, att_e = no_structural_abandonment_conclusion(live, a, N, eligible=NOT_A)
        self.assertFalse(dead_e)
        self.assertEqual(att_e, Q(0))

    def test_proof_as_evidence_not_service(self):
        """A's proof cited as a ground by an eligible reviewer's receipt: the attention
        counted is the reviewer's, however much A wrote."""
        a = [{"A": Q(10), "reviewer": Q(1)}]
        self.assertEqual(attention(a, 1, eligible=NOT_A), Q(1))

    def test_transport_feasibility_shrinks_to_eligible_capacity(self):
        claims = [Q(1), Q(1)]
        capacity = [{"A": Q(1), "reviewer": Q(1, 2)}, {"A": Q(1), "reviewer": Q(1, 2)}]
        self.assertTrue(feasible_with_eligibility(claims, capacity, H=0, eligible=lambda s: True))
        self.assertFalse(feasible_with_eligibility(claims, capacity, H=0, eligible=NOT_A))
        capacity2 = [{"reviewer": Q(1, 2)}, {"reviewer": Q(1, 2)}, {"reviewer": Q(1)}]
        claims2 = [Q(1), Q(1), Q(0)]
        self.assertTrue(feasible_with_eligibility(claims2, capacity2, H=1, eligible=NOT_A))
        self.assertFalse(feasible_with_eligibility(claims2, capacity2, H=0, eligible=NOT_A))


if __name__ == "__main__":
    unittest.main()
