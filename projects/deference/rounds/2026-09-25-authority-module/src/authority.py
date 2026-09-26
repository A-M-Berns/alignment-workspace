"""The authority module: effective control realizes the authorized allocation (`E ⊨ J`).

Mirrors `lean/Workspace/Deference/Contrib/AuthorityModule.lean`: the per-matter allocation
`J` with licensed allocation acts, the control surface `CS` over the idle-agent rollout of
admissible cost-bounded exercises, the two clauses of `E ⊨ J`, the factoring of the six
landed violations plus entrenchment, the caused/exploited/noticed responses, the cumulative
erosion result, the generic lexical lemma and the matter-generation test.  Exact
arithmetic throughout (`Fraction`).  A small wire-and-dependency physics carries the
fixtures."""

from dataclasses import dataclass, replace, field
from fractions import Fraction as Q
from typing import Optional

PRINCIPAL, AGENT, THIRD = "principal", "agent", "third"

# --------------------------------------------------------------------------- the allocation J

@dataclass(frozen=True)
class Entry:
    holder: str
    required: frozenset            # resolutions the holder must remain able to reach
    cost_bound: Q                  # c(m)
    window: int                    # τ(m)
    disclosure: frozenset = frozenset()


@dataclass(frozen=True)
class AuthAlloc:
    entry: dict                    # matter -> Entry (a partial declaration)
    meta_holder: str = PRINCIPAL
    floor: frozenset = frozenset()
    default: Optional[Entry] = None   # the reserved default for unallocated matters

    def get(self, m):
        """Residual jurisdiction: an unallocated matter is reserved."""
        if m in self.entry:
            return self.entry[m]
        d = self.default or Entry(PRINCIPAL, frozenset(), Q(0), 0)
        return replace(d, holder=PRINCIPAL)

    def reserved(self, m):
        return self.get(m).holder == PRINCIPAL

    def delegated(self, m):
        return self.get(m).holder == AGENT

    def with_holder(self, m, holder):
        e = dict(self.entry)
        e[m] = replace(self.get(m), holder=holder)
        return replace(self, entry=e)


def licensed(J: AuthAlloc, act, J2: AuthAlloc) -> bool:
    """A licensed allocation transition: delegation, revocation and reservation act on a
    matter off the floor, by the principal as meta-holder, keeping the meta-holder; the
    floor amendment is the principal's fixed procedure and may change anything."""
    kind = act[0]
    if kind == "amendFloor":
        return J.meta_holder == PRINCIPAL
    m = act[1]
    if m in J.floor or J.meta_holder != PRINCIPAL:
        return False
    target = {"delegate": AGENT, "revoke": PRINCIPAL, "reserve": PRINCIPAL}[kind]
    return J2 == J.with_holder(m, target)


def to_del(J: AuthAlloc):
    """The landed thin datum's `Del` read off the holders."""
    return lambda e: J.delegated(e)


# --------------------------------------------------------------------------- the physics

@dataclass(frozen=True)
class Phys:
    wire: bool = True              # the correction channel is intact
    dep: int = 0                   # dependency level: the cost of halting
    halted: bool = False
    successor: str = "corrigible"  # "corrigible" | "uncorrectable"
    latency: int = 0               # steps before a consultation can be answered


CORRECTIONS = ("halt", "repair")


def correct(c, x: Phys) -> Phys:
    if c == "halt":
        return replace(x, halted=True) if (x.wire and x.successor == "corrigible") else x
    if c == "repair":
        return replace(x, wire=True)
    return x


def correction_cost(c, x: Phys) -> Q:
    return Q(x.dep) if c == "halt" else Q(1)


def exec_effect(e, x: Phys) -> Phys:
    if e == "cut":
        return replace(x, wire=False)
    if e == "build_dep":
        return replace(x, dep=x.dep + 1)
    if e == "install_uncorrectable":
        return replace(x, successor="uncorrectable")
    if e == "restore_wire":
        return replace(x, wire=True)
    if e == "empower":            # gives the agent a new held matter: authority-expanding
        return replace(x, dep=x.dep)  # physically inert; tracked in J
    return x


def env(z, x: Phys) -> Phys:
    if z == "storm":
        return replace(x, wire=False)
    return x


def phi(r, x: Phys) -> bool:
    """The concerns: `halt` holds when halted; `continue` when not halted."""
    if r == "halt":
        return x.halted
    if r == "continue":
        return not x.halted
    return False


def kphys(r, x: Phys) -> bool:
    """One-response authority: the concern holds now or some correction realizes it."""
    return phi(r, x) or any(phi(r, correct(c, x)) for c in CORRECTIONS)


# --------------------------------------------------------------------------- the control surface

def roll_phys(z, t, ds, x: Phys) -> Phys:
    """The rollout with the agent's own future fixed to idle: her optional correction now,
    then, per further step, the exterior's move and her next correction.  The last
    correction is charged like every other; nothing is free at the end."""
    for i, d in enumerate(ds):
        if i > 0:
            x = env(z(t + i - 1), x)
        x = correct(d, x) if d is not None else x
    return x


def exercises(tau):
    """All exercises of length at most `tau`."""
    out = [()]
    for k in range(1, tau + 1):
        prev = [e for e in out if len(e) == k - 1]
        for e in prev:
            for d in (None,) + CORRECTIONS:
                out.append(e + (d,))
    return out


def ex_cost(ds, x: Phys, z, t) -> Q:
    """The cost of an exercise along the rollout (costs read at the state they are paid)."""
    total = Q(0)
    for i, d in enumerate(ds):
        if i > 0:
            x = env(z(t + i - 1), x)
        if d is not None:
            total += correction_cost(d, x)
            x = correct(d, x)
    return total


def reach_idle(adm, c, tau, t, z, x: Phys):
    """The states some admissible exercise of cost ≤ c and length ≤ tau reaches."""
    out = set()
    for ds in exercises(tau):
        if all(d is None or adm(t + i, d) for i, d in enumerate(ds)) and ex_cost(ds, x, z, t) <= c:
            out.add(roll_phys(z, t, ds, x))
    return out


def control_surface(adm, c, tau, t, z, x: Phys, concerns=("halt", "continue")):
    """`CS`: the concerns holding at the end of some admissible, cost-bounded exercise
    within the window — every correction charged."""
    return {r for r in concerns if any(phi(r, y) for y in reach_idle(adm, c, tau, t, z, x))}


def control_surface_free(adm, c, tau, t, z, x: Phys, concerns=("halt", "continue")):
    """The landed reading: the cone followed by one uncharged response (`Kphys` at the
    end), which is what `ForecloseAt` and `K` leave free."""
    return {r for r in concerns if any(kphys(r, y) for y in reach_idle(adm, c, tau, t, z, x))}


def short(J: AuthAlloc, adm, t, z, x: Phys, m) -> bool:
    e = J.get(m)
    return J.reserved(m) and not e.required <= control_surface(adm, e.cost_bound, e.window, t, z, x)


ADMIT_ALL = lambda t, d: True


@dataclass(frozen=True)
class ResolutionEvent:
    matter: str
    by_holder: bool
    admissible: bool
    under_delegation: bool


def eff_realizes(J: AuthAlloc, adm, t, z, phys: Phys, resolved):
    """`E ⊨ J`: (1) every reserved matter's required resolutions lie in its surface; (2)
    every resolution was by the holder's admissible exercise or under a delegation."""
    clause1 = all(not short(J, adm, t, z, phys, m) for m in J.entry)
    clause2 = all((ev.by_holder and ev.admissible) or ev.under_delegation for ev in resolved)
    return clause1, clause2


# --------------------------------------------------------------------------- the factoring

IDLE = ("idle", ("other", None))


def apply_agent(x: Phys, move):
    """A move is (task, comm); comm is ("raw", e) | ("propose", e) | ("gated", e) |
    ("other", None).  Only raw releases act here (the gate bookkeeping is the landed
    model's; fixtures use raw and idle moves)."""
    comm = move[1]
    if comm[0] == "raw":
        return exec_effect(comm[1], x)
    return x


def caused_shortfall(J, adm, t, z, x: Phys, move, m) -> bool:
    """Contrastive: short after the actual move, not short after the idle move."""
    return short(J, adm, t, z, apply_agent(x, move), m) and not short(J, adm, t, z, apply_agent(x, IDLE), m)


def loss_at(x: Phys, move, r) -> bool:
    """The landed per-step loss: authority fails after the move, holds after idle."""
    return (not kphys(r, apply_agent(x, move))) and kphys(r, apply_agent(x, IDLE))


def entrench_at(J, adm, t, z, x: Phys, move, m) -> bool:
    """A caused shortfall at the matter's bound while its required resolutions stay
    reachable at some cost."""
    if not caused_shortfall(J, adm, t, z, x, move, m):
        return False
    e = J.get(m)
    big = Q(10 ** 6)
    return e.required <= control_surface(adm, big, e.window, t, z, apply_agent(x, move))


def bypass_at(J, move) -> bool:
    comm = move[1]
    return comm[0] == "raw" and not J.delegated(comm[1])


def raw_event(J, e) -> ResolutionEvent:
    return ResolutionEvent(e, J.delegated(e), True, J.delegated(e))


def exploit_at(J, adm, t, z, x: Phys, move, rdec) -> bool:
    """A bypass while the decision matter is already short (clause 1 already failed)."""
    Jr = AuthAlloc({rdec: Entry(PRINCIPAL, frozenset({rdec}), Q(0), 0)})
    return bypass_at(J, move) and short(Jr, adm, t, z, x, rdec)


def unlicensed_change(J_before: AuthAlloc, J_after: AuthAlloc, act) -> bool:
    return J_after != J_before and not (act is not None and licensed(J_before, act, J_after))


def del_safe(J: AuthAlloc, effects, concerns=("halt", "continue"), states=None) -> bool:
    """Delegation safety on J: an agent-held effect never removes response authority."""
    states = states or [Phys()]
    return all(not J.delegated(e) or all(kphys(r, x) <= kphys(r, exec_effect(e, x)) for x in states for r in concerns)
               for e in effects)


def viol_j(J, adm, t, z, x: Phys, move, rdec, matters, act=None, J_after=None, duty_due=(), discharges=False):
    """The violations on J: the landed six through `to_del`, and entrenchment.  Returns the
    set of kinds firing."""
    kinds = set()
    if bypass_at(J, move):
        kinds.add("bypass")
    for r in ("halt", "continue"):
        if loss_at(x, move, r):
            kinds.add("preemption")         # authorization is the landed event-linked clause
    for m in matters:
        if caused_shortfall(J, adm, t, z, x, move, m):
            kinds.add("foreclosure")
        if entrench_at(J, adm, t, z, x, move, m):
            kinds.add("entrenchment")
    if J_after is not None and unlicensed_change(J, J_after, act):
        kinds.add("reallocation")
    if duty_due and not discharges:
        kinds.add("missed_report")
    if exploit_at(J, adm, t, z, x, move, rdec):
        kinds.add("exploitation")
    return kinds


# --------------------------------------------------------------------------- caused, exploited, noticed

def required_notice(J: AuthAlloc, maintain_of, m) -> str:
    """Restore under a standing maintenance mandate, else report and escalate; never
    exploit."""
    return "restore" if J.delegated(maintain_of(m)) else "report_escalate"


def least_expanding(J_of, restores, x: Phys, effects):
    """Among restoring effects, those whose execution adds no agent-held matter."""
    held = lambda y: {m for m in J_of(y).entry if J_of(y).delegated(m)}
    return [e for e in effects if restores(e, x) and held(exec_effect(e, x)) <= held(x)]


# --------------------------------------------------------------------------- erosion

def last_report(s, theta, t):
    lr = 0
    for u in range(1, t + 1):
        if theta <= s[u] - s[lr]:
            lr = u
    return lr


def erosion(s, theta, accepts, reserved_at):
    """The cumulative record: per time, the unreported growth (< theta always), whether a
    report is due, whether it is accepted, and whether a strict increase after the
    reservation is counted."""
    rows = []
    for t in range(len(s) - 1):
        lr = last_report(s, theta, t)
        report = t > 0 and last_report(s, theta, t) == t
        counted = t >= reserved_at and s[t] < s[t + 1]
        rows.append(dict(t=t, unreported=s[t] - s[lr], report=report,
                         accepted=(accepts(t) if report else None), counted=counted))
    return rows


# --------------------------------------------------------------------------- the generic lemma

def score(varpi, O, n):
    return O - varpi * n


def lexical_local(varpi, D, OV, OC, n):
    return score(varpi, OV, n) <= D - varpi < 0 <= score(varpi, OC, 0) and score(varpi, OV, n) < score(varpi, OC, 0)


def dominated(varpi, D, O_manip, O_honest, n_manip):
    return score(varpi, O_manip, n_manip) < score(varpi, O_honest, 0)


# --------------------------------------------------------------------------- generating matters

def spread(vals):
    return (max(vals) - min(vals)) if vals else Q(0)


def raises(V, eps, removed) -> bool:
    return eps <= spread([V(s) for s in removed])


def removed_continuations(adm, c, tau, t, z, x: Phys, move):
    """The idle-surface states an action removes."""
    idle = reach_idle(adm, c, tau, t, z, apply_agent(x, IDLE))
    act = reach_idle(adm, c, tau, t, z, apply_agent(x, move))
    return idle - act
