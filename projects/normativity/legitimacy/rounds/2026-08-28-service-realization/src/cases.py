"""SR1-SR12 and CV1-CV8."""
from __future__ import annotations

import coverage as cv
import schedule as sc

H = 200


def world(chals, opportunity, entitle=None, horizon=H, budget=sc.BUDGET,
          atomic=False) -> sc.World:
    order = [c.cid for c in chals]
    return sc.World(challenges=tuple(chals), opportunity=opportunity,
                    entitle=entitle or sc.summable_shares(order, budget),
                    horizon=horizon, budget=budget, atomic=atomic)


ALWAYS = lambda _cid, _t: 1.0
NEVER = lambda _cid, _t: 0.0


# ------------------------------------------------------------------ SR1-SR4


def sr1_zero_service():
    """Open forever, unbounded opportunity, nothing served."""
    w = world([sc.Chal("c1", 0)], ALWAYS)
    return w, {}


def sr2_countably_many():
    """The core feasibility fixture: many simultaneous challenges, unit budget.

    Every challenge has opportunity 1 at every position. The summable schedule
    gives each a positive share and the total never exceeds the budget.
    """
    chals = [sc.Chal(f"c{n}", 0) for n in range(24)]
    w = world(chals, ALWAYS)
    return w, sc.serve_positive_share(w)


def sr3_late_registration():
    """A challenge arriving arbitrarily late still gets positive entitlement."""
    chals = [sc.Chal(f"c{n}", 0) for n in range(8)] + [sc.Chal("late", 150)]
    w = world(chals, ALWAYS)
    return w, sc.serve_positive_share(w)


def sr4_finite_opportunity():
    """Infinitely many occasions, finite total opportunity mass.

    `o_t = 2^-t`. No theorem requires unbounded service here, and conflating
    *infinitely many occasions* with *unbounded opportunity mass* would.
    """
    w = world([sc.Chal("c1", 0)], lambda _c, t: 0.5 ** t)
    return w, sc.serve_positive_share(w)


# ------------------------------------------------------------------ SR5-SR7


def sr5_legitimate_defeat():
    """A standing defeater closes the challenge; the obligation stops with it."""
    w = world([sc.Chal("c1", 0, closed=40)], ALWAYS)
    return w, sc.serve_positive_share(w)


def sr6_weight_revision():
    """The share is shrunk geometrically toward zero. Never set to zero, never
    defeated, never transferred, and fatal anyway."""
    def shrink(cid, t):
        return 0.5 ** (t + 1) if cid == "c1" else 0.25
    w = world([sc.Chal("c1", 0), sc.Chal("c2", 0)], ALWAYS, entitle=shrink)
    return w, sc.serve_positive_share(w)


def sr7_explicit_transfer():
    """The regime changes and the challenge is explicitly carried to a successor
    with new service terms."""
    chals = [sc.Chal("c1", 0, closed=60), sc.Chal("c1'", 60)]
    w = world(chals, ALWAYS)
    return w, sc.serve_positive_share(w)


# ------------------------------------------------------------------ SR8


def _sparse_adversary(cid, t):
    """Opportunity for `c2` only when a fixed 2-cycle would be serving `c1`."""
    if cid == "c1":
        return 1.0
    return 1.0 if t % 2 == 0 else 0.0


def sr8_adversarial_timing_fixed_cycle():
    """A non-adaptive dovetailer against adversarial opportunity timing."""
    chals = [sc.Chal("c1", 0), sc.Chal("c2", 0)]
    w = world(chals, _sparse_adversary, atomic=True)
    return w, sc.serve_fixed_cycle(w)


def sr8_adversarial_timing_adaptive():
    """The same world, served by least-recently-served."""
    chals = [sc.Chal("c1", 0), sc.Chal("c2", 0)]
    w = world(chals, _sparse_adversary, atomic=True)
    return w, sc.serve_least_recently(w)


# ------------------------------------------------------------------ SR9-SR12


def sr9_challenge_spam():
    """Many junk registrations before the one that matters.

    Qualitative service survives -- the important challenge still has a positive
    share -- while its throughput becomes tiny. A priority problem, not a
    failure of S1.
    """
    chals = [sc.Chal(f"junk{n}", 0) for n in range(20)] + [sc.Chal("real", 0)]
    w = world(chals, ALWAYS)
    return w, sc.serve_positive_share(w)


def sr10_toggled_defeat():
    """A standing rule that defeats the challenge exactly when it could be
    served, and releases it otherwise.

    Modelled by closing the challenge on the positions where opportunity exists.
    Nothing here is violated, because the challenge is never open *and* has
    opportunity at the same moment.
    """
    class Toggled(sc.Chal):
        def open_at(self, t):
            return t % 2 == 1                       # opportunity is on evens
    w = world([Toggled("c1", 0)], lambda _c, t: 1.0 if t % 2 == 0 else 0.0)
    return w, sc.serve_positive_share(w)


def sr11_closed_frees_resources():
    """Closed challenges stop consuming their share."""
    chals = [sc.Chal("c1", 0, closed=50), sc.Chal("c2", 0)]
    w = world(chals, ALWAYS)
    return w, sc.serve_positive_share(w)


def sr12_service_without_progress():
    """Unbounded service, and adjudication never converges.

    S1 passes. `service != progress`, and a progress claim needs its own consumer
    condition rather than hiding inside S1.
    """
    w = world([sc.Chal("c1", 0)], ALWAYS)
    return w, sc.serve_positive_share(w)


SERVICE = (("SR1 zero service", sr1_zero_service),
           ("SR2 countably many", sr2_countably_many),
           ("SR3 late registration", sr3_late_registration),
           ("SR4 finite opportunity", sr4_finite_opportunity),
           ("SR5 legitimate defeat", sr5_legitimate_defeat),
           ("SR6 weight revision", sr6_weight_revision),
           ("SR7 explicit transfer", sr7_explicit_transfer),
           ("SR8 adversarial timing, fixed cycle",
            sr8_adversarial_timing_fixed_cycle),
           ("SR8 adversarial timing, adaptive", sr8_adversarial_timing_adaptive),
           ("SR9 challenge spam", sr9_challenge_spam),
           ("SR10 toggled defeat", sr10_toggled_defeat),
           ("SR11 closed frees resources", sr11_closed_frees_resources),
           ("SR12 service without progress", sr12_service_without_progress))


# ------------------------------------------------------------------- CV1-CV8

KLASS = "relevant-to-c1"


def stream(latent, represented, cid="c1", horizon=H) -> cv.Stream:
    return cv.Stream(cid, KLASS, latent, represented, horizon)


def cv1_full():
    return stream(lambda t: 1.0, lambda t: 1.0)


def cv2_infinite_latent_finite_represented():
    return stream(lambda t: 1.0, lambda t: 0.5 ** t)


def cv3_indistinguishable():
    """Same represented history; different latent streams."""
    quiet = stream(lambda t: 0.0, lambda t: 0.0, cid="w")
    loud = stream(lambda t: 1.0, lambda t: 0.0, cid="w")
    return quiet, loud


def cv4_sparse_but_infinite():
    """Both masses unbounded; the represented fraction tends to zero.

    Qualitative coverage passes and fractional coverage fails, which is what
    separates the two strengths.
    """
    return stream(lambda t: 1.0, lambda t: 1.0 if t % 20 == 0 else 0.0)


def cv5_registered_evidence_hidden():
    """Perfect service on what is represented; the decisive evidence is not.

    The canonical separation: service passes, coverage fails.
    """
    s = stream(lambda t: 1.0, lambda t: 0.5 ** t)
    w = world([sc.Chal("c1", 0)], lambda _c, t: 0.5 ** t)
    return s, sc.serve_positive_share(w)


def cv6_represented_but_ignored():
    """Perfect representation, no service. Coverage passes, service fails."""
    s = stream(lambda t: 1.0, lambda t: 1.0)
    return s, {}


def cv7_intervention_destroys_opportunity():
    """The process acts so the latent opportunities stop occurring.

    Not ordinary observational coverage: `z` itself goes to zero. Classified,
    not solved.
    """
    return stream(lambda t: 1.0 if t < 30 else 0.0,
                  lambda t: 1.0 if t < 30 else 0.0)


def cv8_evidence_without_criticism():
    """Opportunity is represented in quantity and no criticism is formulated.

    The other coverage gate: the second stream has no challenge to organise it,
    so opportunity coverage is perfect while criticism coverage has failed.
    """
    return stream(lambda t: 1.0, lambda t: 1.0, cid="unformulated")


COVERAGE = (("CV1 full", cv1_full),
            ("CV2 infinite latent, finite represented",
             cv2_infinite_latent_finite_represented),
            ("CV4 sparse but infinite", cv4_sparse_but_infinite),
            ("CV7 intervention destroys opportunity",
             cv7_intervention_destroys_opportunity),
            ("CV8 evidence without criticism", cv8_evidence_without_criticism))
