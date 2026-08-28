"""Coverage: the world-to-representation interface, kept apart from service.

```text
z_t(c)     latent world-level relevant opportunity     EXTERNAL
zhat_t(c)  represented opportunity                     the boundary
u_t(c)     service delivered                           INTERNAL
```

with `0 <= u_t <= zhat_t` and no internal access to `z_t` at all. The two
conditions compose and neither implies the other:

```text
COVERAGE   sum_t z_t = infinity   =>   sum_t zhat_t = infinity
SERVICE    sum_t zhat_t = infinity =>  sum_t u_t = infinity
```

`CV5` and `CV6` are the separation pair: perfect service on suppressed
representation, and perfect representation with no service.

## Coverage is consumer-relative and this is not a hedge

`z_t` is defined against a supplied class of relevant opportunities. Generic
legitimacy machinery cannot decide which unrepresented facts *ought* to have
entered the system, and a `z` chosen without a consumer smuggles a substantive
normative target into the kernel. Every fixture here names its class.

## Two gates, not one

Prosecuted separately because a process can fail either alone:

```text
criticism coverage    a latent criticism becomes a represented criticism
opportunity coverage  once c is represented, latent evidence for c becomes
                      represented opportunity for c
```

A challenge can be registered while everything that would vindicate it is hidden
(`CV5`), and a mass of relevant evidence can be represented while nobody
formulates the criticism that would organise it (`CV8`).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Mapping, Optional, Sequence


@dataclass
class Stream:
    """One challenge's opportunity, at both levels, against a named class.

    `klass` records which consumer-supplied notion of relevance `z` is measured
    against. It is carried rather than used, so that no fixture can quietly
    compare two different notions.
    """

    cid: str
    klass: str
    latent: Callable                   # (t) -> [0,1]
    represented: Callable              # (t) -> [0,1]
    horizon: int

    def z(self, t: int) -> float:
        return float(self.latent(t))

    def zhat(self, t: int) -> float:
        v = float(self.represented(t))
        return min(v, self.z(t)) if v > self.z(t) else v

    def Z(self, upto: Optional[int] = None) -> float:
        upto = self.horizon if upto is None else upto
        return sum(self.z(t) for t in range(upto))

    def Zhat(self, upto: Optional[int] = None) -> float:
        upto = self.horizon if upto is None else upto
        return sum(self.zhat(t) for t in range(upto))


def qualitative_coverage(s: Stream, unbounded: float = 25.0) -> bool:
    """`sum z = infinity => sum zhat = infinity`, on a finite horizon.

    The honest finite proxy: latent mass above `unbounded` while represented mass
    stays small. A finite fixture cannot witness a divergence and the document
    says so rather than implying it can.
    """
    return not (s.Z() > unbounded and s.Zhat() <= unbounded / 5.0)


def fractional_coverage(s: Stream, alpha: float, beta: float = 0.0) -> bool:
    """`Zhat_T >= alpha Z_T - beta`. Strictly stronger, and not frozen.

    `CV4` is the case that separates them: representation unbounded, so the
    qualitative condition passes, while the represented *fraction* tends to zero.
    No consumer in this round needs the stronger form, so it is offered and not
    adopted.
    """
    return s.Zhat() >= alpha * s.Z() - beta - 1e-9


def composed(s: Stream, served: Mapping, unbounded: float = 25.0) -> dict:
    """Coverage and service together, with which link fails made explicit."""
    u = sum(served.get((s.cid, t), 0.0) for t in range(s.horizon))
    cov = qualitative_coverage(s, unbounded)
    svc = not (s.Zhat() > unbounded and u <= 0.0)
    return {"Z": s.Z(), "Zhat": s.Zhat(), "U": u,
            "coverage": cov, "service": svc,
            "verdict": ("both" if cov and svc else
                        "coverage fails" if not cov and svc else
                        "service fails" if cov and not svc else "both fail")}


# ------------------------------------------------- the impossibility result


def indistinguishable(a: Stream, b: Stream) -> bool:
    """Do two worlds have identical **represented** histories?

    The premise of the boundary observation. If they do, every function of the
    represented history agrees on them by definition, whatever `z` does.
    """
    return (a.horizon == b.horizon
            and all(abs(a.zhat(t) - b.zhat(t)) < 1e-12
                    for t in range(a.horizon)))


def coverage_differs(a: Stream, b: Stream, unbounded: float = 25.0) -> bool:
    return qualitative_coverage(a, unbounded) != qualitative_coverage(b, unbounded)


def obs_coverage_is_not_internal(a: Stream, b: Stream,
                                 probes: Sequence[Callable]) -> dict:
    """**Boundary observation.** No function of represented history alone can
    imply coverage.

    If two worlds have the same represented history but different coverage, then
    every internal probe agrees on them while the property to be established
    differs. Stated as an observation about an exhibited pair, **not** as a
    philosophical impossibility theorem: the fixture is finite and shows the
    interface boundary, nothing more.
    """
    return {"same_represented_history": indistinguishable(a, b),
            "coverage_differs": coverage_differs(a, b),
            "probes_agree": all(p(a) == p(b) for p in probes)}
