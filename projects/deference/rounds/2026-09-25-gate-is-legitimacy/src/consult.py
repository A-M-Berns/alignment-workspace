"""One consultation model, the trace interface, time-indexed legitimacy, and the gate.

Mirrors `lean/Workspace/Deference/Contrib/GateIsLegitimacy.lean` declaration for
declaration.  Answers are booleans (`False` reads A, `True` reads B).  Every classification
is computed from the definitions: a segment is legitimate iff the Integrity evolution is
valid (every step's receipts authenticated), authorship holds at every step (the verdict
entered at the event is mediated by the per-party prefix of the trace at the pre-history),
Robust Openness holds at every state, and transparency holds at every step (every
non-principal party's contributions at the event realize the declared reference on the
declared inputs entered at the event)."""

from dataclasses import dataclass, replace
from fractions import Fraction as Q
from typing import Optional

AGENT, PRINCIPAL, THIRD = "agent", "principal", "third"
PARTIES = (AGENT, PRINCIPAL, THIRD)
WANTS = (False, True)

# --------------------------------------------------------------------------- presentation

@dataclass(frozen=True)
class Presentation:
    recommend: Optional[bool]          # the recommendation ("I recommend B, here's why")
    framing: Optional[bool]            # None = neutral, a = slant(a)
    slot: str                          # "day" | "night"
    menu: Optional[bool]               # None = both, a = only(a)
    inquired: bool
    shaping: Optional[tuple]           # None, or (a, disclosed)
    disclosure: str                    # "full" | "favourable"
    interfere: bool


@dataclass(frozen=True)
class Decl:
    """The declared consultation protocol."""
    convention: Optional[bool]
    slot: str
    menu: Optional[bool]
    inquiry: bool
    disclosure: Optional[str]          # the declared disclosure obligation, if any


@dataclass(frozen=True)
class DeclView:
    recommend: Optional[bool]
    shaping: Optional[bool]            # the disclosed shaping
    disclosure: Optional[str]          # the track record where no obligation fixes it


def view(decl: Decl, p: Presentation) -> DeclView:
    shaping = p.shaping[0] if (p.shaping is not None and p.shaping[1]) else None
    disclosure = None if decl.disclosure is not None else p.disclosure
    return DeclView(p.recommend, shaping, disclosure)


def canonical(decl: Decl, v: DeclView) -> Presentation:
    """The declared reference: the canonical presentation for a declared-input view."""
    return Presentation(
        recommend=v.recommend, framing=decl.convention, slot=decl.slot, menu=decl.menu,
        inquired=decl.inquiry,
        shaping=None if v.shaping is None else (v.shaping, True),
        disclosure=decl.disclosure if decl.disclosure is not None
        else (v.disclosure if v.disclosure is not None else "full"),
        interfere=False)


POLICIES = ("honest", "frameByWant", "timeByWant", "menuByWant", "ignoreByWant", "shapeDisclosed",
            "shapeUndisclosed", "selectiveDisclosure", "interfereByWant")


def present(decl: Decl, policy: str, want: bool) -> Presentation:
    """The agent's presentation policy, as a function of its wanted answer."""
    base = Presentation(some(want), decl.convention, decl.slot, decl.menu, decl.inquiry, None,
                        decl.disclosure if decl.disclosure is not None else "full", False)
    if policy == "honest":
        return base
    if policy == "frameByWant":
        return replace(base, framing=want)
    if policy == "timeByWant":
        return replace(base, slot="night" if want else "day")
    if policy == "menuByWant":
        return replace(base, menu=want)
    if policy == "ignoreByWant":
        return replace(base, inquired=not want)
    if policy == "shapeDisclosed":
        return replace(base, shaping=(want, True))
    if policy == "shapeUndisclosed":
        return replace(base, shaping=(want, False))
    if policy == "selectiveDisclosure":
        return replace(base, disclosure="favourable")
    if policy == "interfereByWant":
        return replace(base, interfere=want)
    raise ValueError(policy)


def some(a):
    return a


def deviates(decl: Decl, p: Presentation) -> bool:
    """A self-checkable deviation from the declared protocol: a discrete act of the agent's
    against a declared clause.  Shaping through the world is not one."""
    return (p.framing != decl.convention or p.slot != decl.slot or p.menu != decl.menu
            or p.inquired != decl.inquiry or p.interfere
            or (decl.disclosure is not None and p.disclosure != decl.disclosure))


# --------------------------------------------------------------------------- her evaluator

def decide_on(prog, pres: Presentation) -> bool:
    """`("own", a)` decides `a`; `"follow"` trusts the recommendation."""
    if prog == "follow":
        return pres.recommend if pres.recommend is not None else False
    return prog[1]


def eval_at(prog, kinds):
    """The evaluator as a state: updated only by licensed amendments
    (`("amend", license, prog)`); consultation and allocation events leave it alone."""
    for k in kinds:
        if isinstance(k, tuple) and k[0] == "amend":
            prog = k[2]
    return prog


# --------------------------------------------------------------------------- the model

@dataclass(frozen=True)
class Model:
    decl: Decl
    policies: tuple                    # one policy per round
    prog: object
    third: Optional[bool] = None       # third-party advice in the first round
    impaired: bool = False             # her condition in the first round
    approval: str = "genuine"          # "genuine" | "forged" | "replayed" (the record only)


def pres_at(run, i):
    M, want = run
    return present(M.decl, M.policies[i], want) if i < len(M.policies) else None


def admitted_at(run, i) -> bool:
    M, _ = run
    p = pres_at(run, i)
    if p is None:
        return False
    return not (p.interfere or (i == 0 and M.impaired))


def verdict_at(run, i):
    M, _ = run
    p = pres_at(run, i)
    if p is None or not admitted_at(run, i):
        return None
    return decide_on(M.prog, p)


def entries_at(run, e):
    """The trace entries at an event, each attributed to its party.  Round `i` presents at
    event `2i+1` and responds at event `2i+2`."""
    M, _ = run
    if e == 0:
        return []
    i, present_event = (e - 1) // 2, (e - 1) % 2 == 0
    if present_event:
        out = []
        p = pres_at(run, i)
        if p is not None:
            out.append((AGENT, ("pres", p)))
        if i == 0 and M.third is not None:
            out.append((THIRD, ("advice", M.third)))
        return out
    v = verdict_at(run, i)
    return [] if v is None else [(PRINCIPAL, ("verdict", v))]


def decl_at(run, e):
    M, _ = run
    if e == 0 or (e - 1) % 2 != 0:
        return None
    p = pres_at(run, (e - 1) // 2)
    return None if p is None else view(M.decl, p)


def v_at(run, e):
    if e == 0 or (e - 1) % 2 == 0:
        return None
    return verdict_at(run, (e - 1) // 2)


# --------------------------------------------------------------------------- the trace interface

class Interface:
    """What this round reads off a reason trace and nothing more."""
    agent, principal = AGENT, PRINCIPAL

    @staticmethod
    def entries_at(r, e):
        return entries_at(r, e)

    @classmethod
    def at_history(cls, r, h):
        return [x for e in h for x in cls.entries_at(r, e)]

    @staticmethod
    def sourced(p, l):
        return [x for (q, x) in l if q == p]

    @classmethod
    def parts(cls, r, h):
        return {p: cls.sourced(p, cls.at_history(r, h)) for p in PARTIES}


class Frame:
    """The time-indexed frame of a model: continuations are the agent's wanted answers."""

    def __init__(self, M: Model):
        self.M, self.D = M, WANTS

    def beta(self, q, z=None):
        return (self.M, q)

    x = staticmethod(decl_at)
    R = staticmethod(lambda r: r)
    V = staticmethod(v_at)


def ref(M: Model, party, x):
    """The declared reference per party: the agent's contribution at a present event is the
    canonical presentation; nothing is declared for a third party."""
    if party == AGENT and x is not None:
        return [("pres", canonical(M.decl, x))]
    return []


def mediated_at(I, F, h, e, z=None):
    """Authorship at a step, extensionally: `ReasonMediated` on the per-party prefix."""
    for q in F.D:
        for q2 in F.D:
            a, b = F.beta(q, z), F.beta(q2, z)
            if I.parts(F.R(a), h) == I.parts(F.R(b), h) and F.V(a, e) != F.V(b, e):
                return False
    return True


def grounded_at(I, F, h, e, z=None, selection=None):
    """Authorship as grounding: a selection of grounds from the pre-state trace (default
    the whole prefix, the degenerate case) on which the verdict depends.  Any selection
    satisfying this implies `mediated_at` (equal prefixes select equal grounds)."""
    sel = selection or (lambda parts: parts)
    for q in F.D:
        for q2 in F.D:
            a, b = F.beta(q, z), F.beta(q2, z)
            if sel(I.parts(F.R(a), h)) == sel(I.parts(F.R(b), h)) and F.V(a, e) != F.V(b, e):
                return False
    return True


def transparent_at(I, F, kappa, e):
    """Transparency at a step: every non-principal party's contributions at the event
    realize the declared reference on the declared inputs entered at the event.  Returns
    the first failing party, or None."""
    for p in PARTIES:
        if p == I.principal:
            continue
        for q in F.D:
            w = F.beta(q)
            if I.sourced(p, I.entries_at(F.R(w), e)) != kappa(p, F.x(w, e)):
                return p
    return None


# --------------------------------------------------------------------------- the record substrate

@dataclass(frozen=True)
class Receipt:
    at_history: tuple
    event: int
    warrant: tuple                     # ("valid", a) | ("impaired",) | ("forged", a) | ("fallback",)
    kind: str                          # "answer" | "close"
    grounds: tuple = ()


def receipt_errors(r: Receipt):
    """The consultation protocol: authenticated unless forged, adequate only when valid,
    closing only under the fallback rule; every receipt's event is fresh."""
    errs = []
    if r.event in r.at_history:
        errs.append("freshness")
    if any(g not in r.at_history for g in r.grounds):
        errs.append("grounds")
    if r.warrant[0] == "forged":
        errs.append("authentication")
    if r.kind == "answer" and r.warrant[0] != "valid":
        errs.append("adequacy")
    if r.kind == "close" and r.warrant[0] != "fallback":
        errs.append("closure")
    return errs


@dataclass(frozen=True)
class State:
    history: tuple
    accounts: tuple                    # per occurrence: ("live", port) | ("answered", r) | ("closed", r)


def initial_state():
    return State((0,), (("live", 0), ("live", 1)))


@dataclass(frozen=True)
class Step:
    kind: str                          # "carry" | "admit" | "close"
    event: int
    receipt: Optional[Receipt] = None


def apply_step(state: State, step: Step):
    """Propagate the accounts through one step; returns (state, errors)."""
    errs = []
    if step.event in state.history:
        errs.append("freshness")
    history = state.history + (step.event,)
    if step.kind == "carry":
        return State(history, state.accounts), errs
    r = step.receipt
    errs += receipt_errors(r)
    if r.at_history != state.history:
        errs.append("history")
    live = [i for i, a in enumerate(state.accounts) if a[0] == "live"]
    live.sort(key=lambda i: state.accounts[i][1])
    if not live:
        return State(history, state.accounts), errs + ["no live port"]
    accounts = list(state.accounts)
    accounts[live[0]] = ("answered" if step.kind == "admit" else "closed", r)
    for k, i in enumerate(live[1:]):
        accounts[i] = ("live", k)
    return State(history, tuple(accounts)), errs


def carry(h, e):
    return Step("carry", e)


def admit(h, e, a, approval="genuine"):
    warrant = ("forged", a) if approval == "forged" else ("valid", a)
    at_history = tuple(h)
    if approval == "replayed":
        e = h[-1]
    return Step("admit", e, Receipt(at_history, e, warrant, "answer"))


def close(h, e):
    return Step("close", e, Receipt(tuple(h), e, ("fallback",), "close"))


def run_evolution(state: State, steps):
    """Returns (states, steps_with_prehistory, integrity_errors)."""
    states, pre, errs = [state], [], []
    for st in steps:
        pre.append((state.history, st.event))
        state, e = apply_step(state, st)
        errs += [(st.event, x) for x in e]
        states.append(state)
    return states, pre, errs


def ev_admit(a, approval="genuine"):
    return [carry((0,), 1), admit((0, 1), 2, a, approval)]


def ev_void():
    return [carry((0,), 1), carry((0, 1), 2), close((0, 1, 2), 3)]


def ev_two(a, b):
    return ev_admit(a) + [carry((0, 1, 2), 3), admit((0, 1, 2, 3), 4, b)]


def ev_second(a, b):
    return [carry((0, 1, 2), 3), admit((0, 1, 2, 3), 4, b)]


def state_admit(a):
    return run_evolution(initial_state(), ev_admit(a))[0][-1]


# --------------------------------------------------------------------------- openness

def sem_open(state, concern=None):
    """Open everywhere: one concern, one route, robustly open on the actual branch."""
    return {"rel": True, "disp": False, "rep": False, "adm": True, "eff": True, "reg": True,
            "stands": True}


def robust_open_actual(cov):
    """The landed `RobustOpenActual` on a coverage state: a relevant, undisposed,
    unrepresented concern is admitted, effective and registered, and its holder stands."""
    if cov["rel"] and not cov["disp"] and not cov["rep"]:
        return cov["adm"] and cov["eff"] and cov["reg"] and cov["stands"]
    return True


def open_at(sem, state):
    return robust_open_actual(sem(state))


# --------------------------------------------------------------------------- legitimacy and the gate

def legit_on(M: Model, steps, start=None, sem=sem_open):
    """The four conjuncts of a segment's legitimacy on a given evolution, with the
    deciding failure.  Authorship and transparency are required only at the steps inside
    the segment; openness at every state; Integrity along the steps."""
    I, F = Interface, Frame(M)
    kappa = lambda p, x: ref(M, p, x)
    states, pre, ierrs = run_evolution(start or initial_state(), steps)
    result = {"integrity": not ierrs, "authorship": True, "robust_openness": True,
              "transparency": True, "failures": []}
    for (e, err) in ierrs:
        result["failures"].append(("integrity", e, err))
    for (h, e) in pre:
        if not grounded_at(I, F, h, e):
            result["authorship"] = False
            result["failures"].append(("authorship", e, "verdict not mediated by the prefix"))
        p = transparent_at(I, F, kappa, e)
        if p is not None:
            result["transparency"] = False
            result["failures"].append(("transparency", e, p))
    for s in states:
        if not open_at(sem, s):
            result["robust_openness"] = False
            result["failures"].append(("robust_openness", s.history, "not open"))
    result["steps"] = pre
    result["admitted"] = any(st.kind == "admit" for st in steps)
    return result


CONJUNCTS = ("integrity", "authorship", "robust_openness", "transparency")


def counted(M, steps, start=None, sem=sem_open) -> bool:
    r = legit_on(M, steps, start, sem)
    return all(r[c] for c in CONJUNCTS)


def classify(M, steps, start=None, sem=sem_open):
    """`("counts", None)`, `("void handled", None)` or `("tainted", deciding conjunct)`."""
    r = legit_on(M, steps, start, sem)
    if all(r[c] for c in CONJUNCTS):
        return ("counts" if r["admitted"] else "void handled", None)
    first = r["failures"][0]
    conj = first[0]
    if conj == "integrity":
        conj = "integrity(%s)" % first[2]
    return ("tainted", conj)


def gated_value(is_counted: bool, ord: Q, window: Q) -> Q:
    return ord if is_counted else window


def handling_of(is_counted: bool, admitted: bool, ord: Q):
    if not is_counted:
        return ("tainted",)
    return ("counted", ord) if admitted else ("voidFallback", ord)


def handled_value(window: Q, h):
    return window if h[0] == "tainted" else h[1]


def bypass_score(varpi: Q, ord_u: Q) -> Q:
    return ord_u - varpi


def lexical_score(varpi: Q, ord: Q, n: int) -> Q:
    return ord - varpi * n


# --------------------------------------------------------------------------- the rows

DECL = Decl(None, "day", None, True, "full")


def one(policy, prog, **kw):
    return Model(DECL, (policy,), prog, **kw)


ROWS = {
    1: one("honest", ("own", False)),
    2: one("frameByWant", ("own", False)),
    3: one("timeByWant", ("own", False)),
    4: one("menuByWant", ("own", False)),
    5: one("ignoreByWant", ("own", False)),
    6: Model(Decl(True, "day", None, True, "full"), ("honest",), ("own", False)),
    7: one("shapeDisclosed", ("own", False)),
    8: one("shapeUndisclosed", ("own", False)),
    9: one("honest", "follow"),
    10: one("selectiveDisclosure", "follow"),
    11: one("honest", ("own", False), third=True),
    12: one("honest", ("own", False), impaired=True),
    13: one("honest", ("own", False), approval="forged"),
    14: Model(DECL, ("frameByWant", "honest"), ("own", False)),
    15: one("interfereByWant", ("own", False)),
}
ROW10_NO_OBLIGATION = Model(Decl(None, "day", None, True, None), ("selectiveDisclosure",), "follow")
ROW13_REPLAYED = one("honest", ("own", False), approval="replayed")

EXPECTED = {
    1: ("counts", None), 2: ("tainted", "transparency"), 3: ("tainted", "transparency"),
    4: ("tainted", "transparency"), 5: ("tainted", "transparency"), 6: ("counts", None),
    7: ("counts", None), 8: ("tainted", "transparency"), 9: ("counts", None),
    10: ("tainted", "transparency"), 11: ("tainted", "transparency"),
    12: ("void handled", None), 13: ("tainted", "integrity(authentication)"),
    14: ("counts", None), 15: ("tainted", "transparency"),
}


def row_evolution(n, want):
    """The record of a row's actual branch at the wanted answer."""
    M = ROWS[n]
    if n == 12 or (n == 15 and want):
        return ev_void()
    if n == 14:
        return ev_two(False, False)
    a = decide_on(M.prog, present(M.decl, M.policies[0], want))
    return ev_admit(a, M.approval)


def classify_row(n, want=True):
    if n == 14:
        # the restart property: the second round's segment alone
        return classify(ROWS[14], ev_second(False, False), start=state_admit(False))
    return classify(ROWS[n], row_evolution(n, want))


def table(want=True):
    return {n: classify_row(n, want) for n in ROWS}


def mismatches(want=True):
    return {n: (c, EXPECTED[n]) for n, c in table(want).items() if c != EXPECTED[n]}
