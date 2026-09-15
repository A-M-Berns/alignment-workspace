"""The margin arithmetic of the feedback boundary.

`a_i` is the market's bypass advantage on occasion `i`, `r_i` the realized (settled)
advantage, `w_i ∈ [0,1]` a weighting.  Expectation Unbiasedness From Feedback says the
weighted bias `Σ w_i (a_i − r_i) / Σ w_i` tends to `0` for every `P`-generable divergent
weighting supported on the settlement schedule.  The fixtures here are the arithmetic
of what that permits and forbids; nothing here runs a logical inductor.
"""
from fractions import Fraction as Q


def weighted_bias(a, r, w, N):
    num = sum((w(i) * (a(i) - r(i)) for i in range(1, N + 1)), Q(0))
    den = sum((w(i) for i in range(1, N + 1)), Q(0))
    return num / den if den > 0 else None


def margin_weighting(a, gamma, delta):
    """`ctsind_δ(a_i > γ)`: a continuous, market-generable weighting supported where the
    market's advantage exceeds `γ`."""
    def w(i):
        return min(Q(1), max(Q(0), (a(i) - gamma) / delta))
    return w


def weight_mass(w, N):
    return sum((w(i) for i in range(1, N + 1)), Q(0))


def bypass_count(a, gamma, N):
    """Occasions up to `N` on which a chooser with switching margin `γ` bypasses."""
    return sum(1 for i in range(1, N + 1) if a(i) > gamma)


def harmonic(N):
    return sum((Q(1, i) for i in range(1, N + 1)), Q(0))
