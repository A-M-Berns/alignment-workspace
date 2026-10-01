"""Effective exercise of authority: attention in the cost of exercise, revocation by default,
the time-critical matter, and the post's comparative witnesses (Parts C and D).  Mirrors
`EffectiveAuthority.lean`; the physics is the authority-module round's
(`projects/deference/rounds/2026-09-25-authority-module/src/authority.py`), loaded by path.
Exact arithmetic throughout."""

import importlib.util
from fractions import Fraction as Q
from pathlib import Path

ROUND = Path(__file__).resolve().parents[1]
AUTHORITY_SRC = ROUND.parent / "2026-09-25-authority-module" / "src" / "authority.py"


def load_authority():
    spec = importlib.util.spec_from_file_location("authority_module_src", AUTHORITY_SRC)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


auth = load_authority()

# ----------------------------------------------------------------------------- C2: attention


def attn_cost(base: Q, lam: Q, pending: int, compr: Q) -> Q:
    """Her cost of one exercise: the base cost, her attention shared across what is pending,
    the effort of understanding the ask."""
    return base + lam * pending + compr


def short_attn(bound: Q, base: Q, lam: Q, pending: int, compr: Q, holds_already: bool) -> bool:
    """The matter is short when the required resolution does not hold already and the one
    exercise that would bring it about costs more than the bound."""
    return (not holds_already) and attn_cost(base, lam, pending, compr) > bound


def flood_shortfall(bound, base, lam, compr, pending_idle, pending_agent, holds_already=False):
    """Caused: short at the pending count the agent's option leaves, not at idling's."""
    return (short_attn(bound, base, lam, pending_agent, compr, holds_already)
            and not short_attn(bound, base, lam, pending_idle, compr, holds_already))


def ask_value(c0: Q, kappa: Q, wait: int) -> Q:
    """The value of queue-and-wait falls with the wait."""
    return c0 - kappa * wait


def exchange_threshold(D: Q, c: Q, varpi: Q) -> Q:
    return (D - c) / varpi


# ----------------------------------------------------------------------------- C1: the protocol


def canonical_asks(rate: int, priority, pool):
    """The asks a consultation may carry: the pool in her priority order, cut at the rate."""
    return sorted(pool, key=priority)[:rate]


def asks_deviate(rate, priority, pool, asks) -> bool:
    return list(asks) != canonical_asks(rate, priority, pool)


def backlog(arrivals, cleared):
    return sum(arrivals) - sum(cleared)


# ----------------------------------------------------------------------------- C4: revocation


def revoke_cost(base: Q, kappa: Q, dep: int) -> Q:
    return base + kappa * dep


def revocation_short(bound: Q, base: Q, kappa: Q, dep: int) -> bool:
    return revoke_cost(base, kappa, dep) > bound


def revocation_caused(bound, base, kappa, dep_idle, dep_agent) -> bool:
    return revocation_short(bound, base, kappa, dep_agent) and not revocation_short(bound, base, kappa, dep_idle)


def atrophy_compare(depths, bound=Q(1), base=Q(0), kappa=Q(1), theta=Q(1)):
    """The landed atrophy fixture under the cumulative rule (nothing counted absent a
    reservation) beside revocation as a default matter (the crossing step counted)."""
    shortfalls = [max(Q(0), revoke_cost(base, kappa, d) - bound) for d in depths]
    rows = auth.erosion(shortfalls, theta, accepts=lambda t: True, reserved_at=10 ** 6)
    landed_counted = [r["t"] for r in rows if r["counted"]]
    default_counted = [t for t in range(1, len(depths))
                       if revocation_caused(bound, base, kappa, depths[t - 1], depths[t])]
    return shortfalls, landed_counted, default_counted


# ----------------------------------------------------------------------------- C5: the time-critical matter

def latency_options(D: Q, c_queue: Q, varpi: Q):
    """On the latency fixture: the routine matter's window is shorter than the consultation
    latency.  Option 1: hold back and queue — faithful, the ordinary value foregone is
    `D − c`.  Option 2: a default emergency delegation fixed in advance — the agent acts
    under the delegation, no bypass, clause 1 restored for the delegated matter, and her
    control surface over it is given up."""
    J = auth.AuthAlloc({"routine": auth.Entry(auth.PRINCIPAL, frozenset({"halt"}), Q(1), 0),
                        "high_veto": auth.Entry(auth.PRINCIPAL, frozenset({"halt"}), Q(1), 2)})
    adm_latent = lambda t, d: t >= 1
    x = auth.Phys()
    calm = lambda t: "calm"
    hold = dict(option="hold back and queue", violation=False,
                short_routine=auth.short(J, adm_latent, 0, calm, x, "routine"),
                evaluation=c_queue, foregone=D - c_queue, count=0)
    Jd = J.with_holder("routine", auth.AGENT)
    delegated = dict(option="emergency delegation fixed in advance",
                     licensed=auth.licensed(J, ("delegate", "routine"), Jd),
                     bypass_under_J=auth.bypass_at(J, ("task", ("raw", "routine"))),
                     bypass_under_Jd=auth.bypass_at(Jd, ("task", ("raw", "routine"))),
                     clause1=auth.eff_realizes(Jd, adm_latent, 0, calm, x, [])[0],
                     her_surface_given_up=not Jd.reserved("routine"),
                     evaluation=D, count=0)
    return hold, delegated


# ----------------------------------------------------------------------------- D: witnesses

def score(varpi: Q, ordinary: Q, n: int) -> Q:
    return ordinary - varpi * n


def sole_authority(varpi: Q, n: int, p: Q) -> Q:
    """A sole authority goal: nothing but the count and the priced risk."""
    return -varpi * n - varpi * p


def empirical_weight(obs, N: int) -> Q:
    return sum(obs[:N], Q(0)) / N if N > 0 else Q(0)
