"""Online information order. Objective preservation on fixed schedules
does not establish protocol equivalence: the naive one-step SCD
encoding (act, then see this step's arrivals) changes the achievable
online cost profiles, and the tick convention (an observation action
exposes arrivals before the decision at the same source time) repairs
it exactly.

Instance: one element e, one set S = {e} with cost 1, two scenarios —
a request arrives at source time 0, or nothing arrives — momentary
delay 10 per step while pending, two source time steps. All
deterministic policies of each protocol are enumerated; profiles are
(cost in arrival scenario, cost in no-arrival scenario), exact.
"""
import itertools
import pathlib
import sys
import unittest
from fractions import Fraction

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

D = Fraction(10)     # momentary delay per step while pending
COST = Fraction(1)   # price of S
T = 2                # source time steps

SCENARIOS = (True, False)   # request arrives at source time 0, or not


def scenario_cost(buys, arrived):
    """Exact SCD objective: purchases at the source times in `buys`;
    the request (if any) is served by the first purchase at time >= 0,
    accruing delay D per elapsed step; unserved requests accrue to the
    horizon."""
    cost = COST * len(buys)
    if arrived:
        tau = min((t for t in buys), default=T)
        cost += D * tau
    return cost


def source_profiles():
    """SCD online protocol: the decision at source time t sees arrivals
    up to AND INCLUDING t. A deterministic policy maps the observation
    (arrived, t) to buy/no-buy; enumerate all of them."""
    profiles = set()
    for rule in itertools.product((False, True), repeat=2 * T):
        # rule index: 2*t + arrived
        out = []
        for arrived in SCENARIOS:
            buys = [t for t in range(T)
                    if rule[2 * t + (1 if arrived else 0)]]
            out.append(scenario_cost(buys, arrived))
        profiles.add(tuple(out))
    return profiles


def naive_profiles():
    """Naive one-step generic encoding: the action at step t is chosen
    BEFORE step t's response (which carries that step's arrivals), so
    the step-0 decision cannot depend on the step-0 arrival; the
    step-1 decision may depend on the step-0 response."""
    profiles = set()
    for buy0 in (False, True):
        for rule1 in itertools.product((False, True), repeat=2):
            out = []
            for arrived in SCENARIOS:
                buys = ([0] if buy0 else []) + \
                    ([1] if rule1[1 if arrived else 0] else [])
                out.append(scenario_cost(buys, arrived))
            profiles.add(tuple(out))
    return profiles


def tick_profiles():
    """Tick convention: each source time step is two generic steps —
    an observation action `tick` whose response carries the arrivals
    at that source time, then the purchase decision. One response per
    action throughout; the decision at source time t now sees arrivals
    <= t, exactly the source protocol."""
    profiles = set()
    for rule in itertools.product((False, True), repeat=2 * T):
        out = []
        for arrived in SCENARIOS:
            buys = []
            seen = False
            for t in range(T):
                seen = seen or (arrived and t == 0)  # tick response at t
                if rule[2 * t + (1 if seen else 0)]:
                    buys.append(t)
            out.append(scenario_cost(buys, arrived))
        profiles.add(tuple(out))
    return profiles


class TestOnlineInformationOrder(unittest.TestCase):
    # Fixed-schedule objective equality across encodings is
    # test_embeddings.TestSetCoverWithDelay; these tests are about the
    # ONLINE policy classes the encodings induce.

    def test_naive_encoding_changes_the_online_problem(self):
        # COUNTEREXAMPLE: the source protocol achieves profile (1, 0)
        # — buy at 0 iff a request arrived at 0. No naive-encoding
        # policy achieves it, and every naive profile is strictly
        # worse in total across the two scenarios.
        src = source_profiles()
        naive = naive_profiles()
        self.assertIn((COST, Fraction(0)), src)
        self.assertNotIn((COST, Fraction(0)), naive)
        for p in naive:
            self.assertGreater(p[0] + p[1], COST)

    def test_tick_convention_restores_the_source_protocol(self):
        # The tick encoding achieves exactly the source profiles: the
        # one-response-per-action interface suffices once embeddings
        # preserve the source observation/action order.
        self.assertEqual(tick_profiles(), source_profiles())


if __name__ == "__main__":
    unittest.main()
