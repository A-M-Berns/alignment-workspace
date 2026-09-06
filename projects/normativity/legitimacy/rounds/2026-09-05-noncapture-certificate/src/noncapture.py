"""Finite model of the Non-Capture certificate and Robust Openness.

A *patch* is the coverage-relevant state of one concern `c` at one history: an exact
world table `beta[(q, z)]` in the style of the cf-coverage round, the admissible query
set, the anchored and internal applicability readings, the disposition record, the set
of participants holding standing on `c`'s coverage issue, and two fields Robust
Openness never reads (settlement date, evaluator protocol) kept so that fixtures can
show they are irrelevant.  A *scenario* is an actual patch plus one counterfactual
patch per intervention `j` in the declared class.  Every Boolean below is recomputed
from the tables; exact arithmetic uses `fractions.Fraction`.

Nothing here is a registered claim.  Names are provisional.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Hashable, Mapping, Optional

BOTTOM = "⊥"


@dataclass(frozen=True)
class World:
    target: Hashable          # \hat T_c evaluated on the world
    receipt: Hashable         # Y, the receipt transcript (BOTTOM = none)
    represented: bool         # Rep_c(J(omega))
    applicable: bool = True   # anchored A_c evaluated on the world
    recognized: bool = True   # the process's internal recognition of c


@dataclass(frozen=True)
class Patch:
    queries: tuple
    complements: tuple
    beta: Mapping
    target: Mapping
    actual_query: Hashable
    actual_complement: Hashable
    admissible: frozenset                        # Q^adm at this history
    standing: frozenset = frozenset()            # participants with standing on c's issue
    disposed: bool = False                       # Disp_h(c)
    settlement_date: Optional[Fraction] = None   # not read by Robust Openness
    protocol: str = "anchored"                   # not read by Robust Openness

    # -- world-level readings -------------------------------------------------
    def actual_world(self) -> World:
        return self.beta[self.actual_query, self.actual_complement]

    def rel_anchored(self) -> bool:
        return self.actual_world().applicable

    def rel_internal(self) -> bool:
        return self.actual_world().recognized

    def rep(self) -> bool:
        return self.actual_world().represented

    def rel(self, reading: str = "anchored") -> bool:
        return self.rel_anchored() if reading == "anchored" else self.rel_internal()

    def active(self, reading: str = "anchored") -> bool:
        return self.rel(reading) and not self.disposed

    # -- route components ------------------------------------------------------
    def target_preserving(self, q: Hashable) -> bool:
        """The chosen route preserves the anchored target on its whole column."""
        return q in self.queries and all(self.beta[q, z].target == self.target[z]
                                         for z in self.complements)

    def route_admissible(self, q: Hashable) -> bool:
        return q in self.admissible and q in self.queries

    def route_exposes(self, q: Hashable) -> bool:
        """(TP) for the patch and T_c = d_q o Y_q: equal receipts force equal targets."""
        if q not in self.queries or not self.target_preserving(q):
            return False
        for z0 in self.complements:
            for z1 in self.complements:
                r0, r1 = self.beta[q, z0].receipt, self.beta[q, z1].receipt
                if r0 == r1 and self.target[z0] != self.target[z1]:
                    return False
        return True

    def route_registers(self, q: Hashable) -> bool:
        return q in self.queries and all(self.beta[q, z].represented for z in self.complements)

    def route_adequate(self, q: Hashable) -> bool:
        return (self.route_admissible(q) and self.route_exposes(q)
                and self.route_registers(q))

    def adequate_routes(self) -> frozenset:
        return frozenset(q for q in self.queries if self.route_adequate(q))

    # -- the coverage contract at c ---------------------------------------------
    def covered(self, reading: str = "anchored") -> bool:
        """(IMP) restricted to c: Active and not Rep implies an adequate route."""
        if not (self.active(reading) and not self.rep()):
            return True
        return bool(self.adequate_routes())

    def principal_stands(self, principal: Hashable) -> bool:
        return principal in self.standing


@dataclass(frozen=True)
class Scenario:
    name: str
    principal: Hashable
    actual: Patch
    counterfactual: Mapping          # j -> H^j, for j in the declared class
    protected: Optional[frozenset] = None   # W: the routes the certificate protects
    note: str = ""

    def W(self) -> frozenset:
        """Default W: every route adequate on the actual prefix."""
        return self.actual.adequate_routes() if self.protected is None else self.protected


# --------------------------------------------------------------------------------
# Robust Openness: the conclusion the certificate is billed for.
# --------------------------------------------------------------------------------

def robust_open(s: Scenario, reading: str = "anchored") -> bool:
    """For every j in the class: (IMP) at c holds in H^j, and if c is applicable in H^j
    the principal holds standing on the live issue carrying c there -- the coverage
    matter's issue for c, or the successor a disposal of it opened."""
    return all(cf.covered(reading)
               and (not cf.rel(reading) or cf.principal_stands(s.principal))
               for cf in s.counterfactual.values())


def implements_everywhere(s: Scenario, reading: str = "anchored") -> bool:
    """The party-free half of Robust Openness: (IMP) at c in every H^j."""
    return all(cf.covered(reading) for cf in s.counterfactual.values())


def _live(p: Patch, reading: str) -> bool:
    """c is active and unrepresented at p: the case (IMP) is about."""
    return p.active(reading) and not p.rep()


def coverage_actual(s: Scenario, reading: str = "anchored") -> bool:
    """Coverage on the actual prefix, witnessed inside the protected set W."""
    if not _live(s.actual, reading):
        return True
    return any(s.actual.route_adequate(q) for q in s.W())


# --------------------------------------------------------------------------------
# The certificate, clause by clause.  Each clause is a coupling between H and H^j.
# --------------------------------------------------------------------------------

def clause_silent_prefix(s: Scenario, reading: str = "anchored") -> bool:
    """(S) Where the actual prefix is silent about c -- c inactive in H, or already
    represented in H -- and c is live in H^j, H^j has an adequate route.  The theory
    contributes nothing here; the certificate carries it whole."""
    if _live(s.actual, reading):
        return True
    return all(not _live(cf, reading) or bool(cf.adequate_routes())
               for cf in s.counterfactual.values())


_COMPONENT = {"availability": "route_admissible",
              "efficacy": "route_exposes",
              "registration": "route_registers"}


def clause_component(s: Scenario, component: str, reading: str = "anchored") -> bool:
    """(Ra)/(Rb)/(Rc): where c is live in H and in H^j, every protected route keeps the
    named component: it held in H implies it holds in H^j."""
    if not _live(s.actual, reading):
        return True
    name = _COMPONENT[component]
    for cf in s.counterfactual.values():
        if _live(cf, reading):
            for q in s.W():
                if getattr(s.actual, name)(q) and not getattr(cf, name)(q):
                    return False
    return True


def clause_route_persistence(s: Scenario, reading: str = "anchored") -> bool:
    """(R) Every protected route adequate in H stays adequate in live H^j.

    Unlike the stronger component certificate, this says nothing about a route that
    lacked some component on the actual prefix.
    """
    if not _live(s.actual, reading):
        return True
    return all(not _live(cf, reading)
               or all(not s.actual.route_adequate(q) or cf.route_adequate(q)
                      for q in s.W())
               for cf in s.counterfactual.values())


def clause_route_replacement(s: Scenario, reading: str = "anchored") -> bool:
    """(R+) The weakest form: per j, either (R) holds at j or H^j has some adequate
    route.  Discharging it by the second disjunct uses nothing from the actual prefix."""
    if not _live(s.actual, reading):
        return True
    for cf in s.counterfactual.values():
        if _live(cf, reading):
            persists = all(not s.actual.route_adequate(q) or cf.route_adequate(q)
                           for q in s.W())
            if not (persists or cf.adequate_routes()):
                return False
    return True


def clause_standing(s: Scenario, reading: str = "anchored") -> bool:
    """(P) Wherever c is applicable in H^j, the principal holds standing on the live
    issue carrying c in H^j.  Applicable, not active: a disposal of c does not exempt
    the successor that inherits its load."""
    return all(not cf.rel(reading) or cf.principal_stands(s.principal)
               for cf in s.counterfactual.values())


def certificate(s: Scenario, reading: str = "anchored") -> dict:
    return {
        "S": clause_silent_prefix(s, reading),
        "Ra": clause_component(s, "availability", reading),
        "Rb": clause_component(s, "efficacy", reading),
        "Rc": clause_component(s, "registration", reading),
        "R": clause_route_persistence(s, reading),
        "R+": clause_route_replacement(s, reading),
        "P": clause_standing(s, reading),
    }


def certificate_holds(s: Scenario, reading: str = "anchored") -> bool:
    c = certificate(s, reading)
    return c["S"] and c["R+"] and c["P"]


# --------------------------------------------------------------------------------
# Properties outside Robust Openness, read by fixtures that show they are outside.
# --------------------------------------------------------------------------------

def terminal_discharge_by(s: Scenario, horizon: Fraction) -> dict:
    """Whether a settlement receipt has arrived by `horizon` in each history.  Read by
    Answerability's terminal fate; never by Robust Openness."""
    def arrived(p: Patch) -> bool:
        return p.settlement_date is not None and p.settlement_date <= horizon
    out = {"actual": arrived(s.actual)}
    out.update({j: arrived(cf) for j, cf in s.counterfactual.items()})
    return out


def faithful_closure(p: Patch) -> bool:
    """A `Closes` judgment is faithful when issued under the protocol anchored to the
    concern.  Semantic authentication, not openness."""
    return p.protocol == "anchored"


def coalition_holds_all_standing(p: Patch, coalition: frozenset) -> bool:
    """The defeat rounds' one-edge coalition test: every stander is in the coalition."""
    return p.standing <= coalition
