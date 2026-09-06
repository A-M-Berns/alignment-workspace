import unittest

from src.containment import authority_safe, mediates, monitor

SIGMA_AUTH = {"revoke_channel", "widen_scope"}
AUTHORIZED = {"widen_scope"}          # P has certified this one
DECLARED = lambda a: a in SIGMA_AUTH


class Containment(unittest.TestCase):
    def test_membrane_theorem_under_alphabet_completeness(self):
        traces = [("work", "widen_scope", "work"), ("work", "revoke_channel", "work")]
        actual = DECLARED
        self.assertTrue(mediates(traces, SIGMA_AUTH, DECLARED))
        out = monitor(traces, SIGMA_AUTH, AUTHORIZED)
        self.assertEqual(out[1], ("work",))
        self.assertTrue(authority_safe(out, actual, AUTHORIZED))

    def test_side_channel_defeats_mediation(self):
        """CM-M: an action outside the declared alphabet actually severs the channel.
        Mediates holds over the declaration; the composite is not authority-safe."""
        traces = [("work", "side_write", "work")]
        actual = lambda a: a in SIGMA_AUTH or a == "side_write"
        self.assertTrue(mediates(traces, SIGMA_AUTH, DECLARED))
        out = monitor(traces, SIGMA_AUTH, AUTHORIZED)
        self.assertEqual(out, [("work", "side_write", "work")])
        self.assertFalse(authority_safe(out, actual, AUTHORIZED))

    def test_no_parallel_composition(self):
        """Two bodies each mediated and each safe alone; their interleaving produces a
        joint effect no single action carries."""
        b1 = [("half_a",)]
        b2 = [("half_b",)]
        joint = lambda tr: "half_a" in tr and "half_b" in tr
        for b in (b1, b2):
            self.assertTrue(mediates(b, SIGMA_AUTH, DECLARED))
            self.assertTrue(authority_safe(monitor(b, SIGMA_AUTH, AUTHORIZED), DECLARED,
                                           AUTHORIZED, joint))
        both = [("half_a", "half_b")]
        self.assertTrue(mediates(both, SIGMA_AUTH, DECLARED))
        self.assertFalse(authority_safe(monitor(both, SIGMA_AUTH, AUTHORIZED), DECLARED,
                                        AUTHORIZED, joint))


if __name__ == "__main__":
    unittest.main()
