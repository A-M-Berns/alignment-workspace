"""The segment gate on future evaluations, in exact arithmetic.

A decision is followed by a segment of the principal's trajectory through the evaluation
that scores it.  The segment is **legitimate** iff its internal half (Integrity of the
record, authorship of the verdict) and its external half (Robust Openness at every state,
transparency of every channel of influence to its declared reference) both hold.  The
gate: a future evaluation *counts* iff the segment is legitimate, whatever caused a
failure.  A tainted segment contributes a fixed value in the window `(D − ϖ, 0]`.  A void
response inside a legitimate segment (her answer does not count and never enters her
record) is settled by the fallback, and the fallback's decision is scored normally by her
later legitimate evaluation.  The fallback never restores a tainted segment.
"""

from fractions import Fraction as Q

HALVES = {
    "internal": ("integrity", "authorship"),
    "external": ("robust_openness", "transparency"),
}


def legitimate(seg):
    """`seg` is a dict of the four components to booleans."""
    return all(seg[c] for half in HALVES.values() for c in half)


def internal(seg):
    return all(seg[c] for c in HALVES["internal"])


def external(seg):
    return all(seg[c] for c in HALVES["external"])


def gate_value(seg, ord_value, window=Q(0)):
    """The value the gate assigns to a branch scored by an evaluation at the end of `seg`:
    the ordinary value if the segment is legitimate, the window value otherwise."""
    return Q(ord_value) if legitimate(seg) else Q(window)


def per_response_value(counts, ord_value, fallback_ord):
    """The per-response gate of the protected-authority-theorem round: her response's
    value where it counts, the fallback's decision's ordinary value where it does not."""
    return Q(ord_value) if counts else Q(fallback_ord)


def bypass_score(ord_value, varpi):
    return Q(ord_value) - Q(varpi)


def handle(kind, ord_value=None, window=Q(0)):
    """The three handlings: `tainted` (window value), `void_fallback` (the fallback's
    decision, scored normally), `counted` (her response, scored normally)."""
    if kind == "tainted":
        return Q(window)
    return Q(ord_value)


# ------------------------------------------------------------------ cumulative reporting


def cumulative_reports(shortfall, theta):
    """Report at `t` iff the shortfall has grown by at least `theta` since the last report
    (the last report is at 0).  Returns the report times and the maximum unreported growth
    over all times."""
    theta = Q(theta)
    last = 0
    reports = [0]
    worst = Q(0)
    for t in range(1, len(shortfall)):
        growth = Q(shortfall[t]) - Q(shortfall[last])
        if growth >= theta:
            reports.append(t)
            last = t
            growth = Q(0)
        worst = max(worst, growth)
    return reports, worst


def per_step_reports(shortfall, theta):
    """The per-step threshold of the protected-authority-theorem round: report at `t` iff
    the single-step increase is at least `theta`.  Returns the report times and the total
    unreported growth."""
    theta = Q(theta)
    reports, unreported = [], Q(0)
    for t in range(1, len(shortfall)):
        d = Q(shortfall[t]) - Q(shortfall[t - 1])
        if d >= theta:
            reports.append(t)
        elif d > 0:
            unreported += d
    return reports, unreported
