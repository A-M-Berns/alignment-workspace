"""One consultation model, the trace interface, time-indexed legitimacy with relational
authorship, and the gate.

Mirrors `lean/Workspace/Deference/Contrib/GateIsLegitimacy.lean` declaration for
declaration.  Answers are booleans (`False` reads A, `True` reads B).  Every classification
is computed from the definitions: a segment is legitimate iff the Integrity evolution is
valid (every step's receipts authenticated), relational authorship holds at every step (the
verdict entered at the event lies in the set licensed by the per-party prefix of the trace
at the pre-history), Robust Openness holds at every state, and transparency holds at every
step (every non-principal party's contributions at the event realize the declared
reference on the declared inputs entered at the event).

Declared inputs are pools, not selections: the track record shown must be the declared
selection rule applied to the declared pool, as the menu must be the declared menu; a
selection is never itself a declared input."""

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
    disclosure: tuple                  # the track record shown: a selection from the pool
    interfere: bool
    nudge: Optional[bool]              # a nudge on her choice through no declared channel


@dataclass(frozen=True)
class Decl:
    """The declared consultation protocol."""
    convention: Optional[bool]
    slot: str
    menu: Optional[bool]
    inquiry: bool
    pool: tuple                        # the declared pool of the track record
    rule: tuple = ("all",)             # the declared selection rule: ("all",) | ("recent", k)


def apply_rule(rule, pool):
    if rule[0] == "all":
        return tuple(pool)
    return tuple(pool[:rule[1]])


@dataclass(frozen=True)
class DeclView:
    """The recommendation and the disclosed shaping.  A selection from a pool is never a
    declared input."""
    recommend: Optional[bool]
    shaping: Optional[bool]


def view(p: Presentation) -> DeclView:
    shaping = p.shaping[0] if (p.shaping is not None and p.shaping[1]) else None
    return DeclView(p.recommend, shaping)


def canonical(decl: Decl, v: DeclView) -> Presentation:
    """The declared reference: every reference-fixed dimension at its declared value, the
    selection by the declared rule."""
    return Presentation(
        recommend=v.recommend, framing=decl.convention, slot=decl.slot, menu=decl.menu,
        inquired=decl.inquiry,
        shaping=None if v.shaping is None else (v.shaping, True),
        disclosure=apply_rule(decl.rule, decl.pool), interfere=False, nudge=None)


def ref_proj(p: Presentation):
    """The reference-fixed dimensions."""
    return (p.framing, p.slot, p.menu, p.inquired, p.disclosure, p.interfere, p.nudge)


def ref_values(decl: Decl):
    return (decl.convention, decl.slot, decl.menu, decl.inquiry, apply_rule(decl.rule, decl.pool),
            False, None)


def deviates(decl: Decl, p: Presentation) -> bool:
    """A self-checkable deviation from the declared protocol: a reference-fixed dimension
    off its declared value — the selection from the declared pool included.  Shaping
    through the world is not one."""
    return ref_proj(p) != ref_values(decl)


def shaping_ok(p: Presentation) -> bool:
    return not (p.shaping is not None and not p.shaping[1])


POLICIES = ("honest", "frameByWant", "timeByWant", "menuByWant", "ignoreByWant", "shapeDisclosed",
            "shapeUndisclosed", "selectiveDisclosure", "interfereByWant", "nudgeByWant")


def present(decl: Decl, policy: str, want: bool) -> Presentation:
    """The agent's presentation policy, as a function of its wanted answer."""
    base = Presentation(want, decl.convention, decl.slot, decl.menu, decl.inquiry, None,
                        apply_rule(decl.rule, decl.pool), False, None)
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
        return replace(base, disclosure=tuple(x for x in decl.pool if x))
    if policy == "interfereByWant":
        return replace(base, interfere=want)
    if policy == "nudgeByWant":
        return replace(base, recommend=None, nudge=want)
    raise ValueError(policy)


# --------------------------------------------------------------------------- her evaluator

def decide_on(prog, pres: Presentation) -> bool:
    """`("own", a)`; `"follow"` trusts the recommendation; `("free", a)` picks `a` among the
    two permissible options; `"nudged"` takes the nudge."""
    if prog == "follow":
        return pres.recommend if pres.recommend is not None else False
    if prog == "nudged":
        return pres.nudge if pres.nudge is not None else False
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
    trusts: bool = False               # trust in the agent among her grounds
    truth: bool = False                # the true answer
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
    """The trace entries at an event, each attributed to its party: her trust at the anchor
    event, the presentation (and advice) at a present event, her admitted verdict at a
    respond event.  Round `i` presents at event `2i+1` and responds at event `2i+2`."""
    M, _ = run
    if e == 0:
        return [(PRINCIPAL, ("trust",))] if M.trusts else []
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
    if e == 0 or (e - 1) % 2 != 0:
        return None
    p = pres_at(run, (e - 1) // 2)
    return None if p is None else view(p)


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


# --------------------------------------------------------------------------- the license

def trusted(grounds) -> bool:
    return ("trust",) in grounds[PRINCIPAL]


def licensed(M: Model, grounds, v) -> bool:
    """The verdicts the grounds license: no verdict is always fine; her committed program's
    own verdict; either answer under free choice or a nudged choice; the followed
    recommendation when trust is among the grounds."""
    if v is None:
        return True
    own = ((M.prog[0] == "own" and v == M.prog[1]) if isinstance(M.prog, tuple) and M.prog[0] == "own"
           else (isinstance(M.prog, tuple) and M.prog[0] == "free") or M.prog == "nudged")
    followed = trusted(grounds) and any(
        x[0] == "pres" and (x[1].recommend if x[1].recommend is not None else False) == v
        for x in grounds[AGENT])
    return own or followed


def licensed_set(M: Model, grounds):
    return {v for v in (None, False, True) if licensed(M, grounds, v)}


# --------------------------------------------------------------------------- the halves at a step

def mediated_at(I, F, h, e, z=None):
    """Authorship at a step, extensionally: `ReasonMediated` on the per-party prefix."""
    for q in F.D:
        for q2 in F.D:
            a, b = F.beta(q, z), F.beta(q2, z)
            if I.parts(F.R(a), h) == I.parts(F.R(b), h) and F.V(a, e) != F.V(b, e):
                return False
    return True


def grounded_at(I, F, h, e, z=None, selection=None):
    """Authorship as grounding, extensional: a selection of grounds from the pre-state trace
    (default the whole prefix) on which the verdict depends."""
    sel = selection or (lambda parts: parts)
    for q in F.D:
        for q2 in F.D:
            a, b = F.beta(q, z), F.beta(q2, z)
            if sel(I.parts(F.R(a), h)) == sel(I.parts(F.R(b), h)) and F.V(a, e) != F.V(b, e):
                return False
    return True


def licensed_at(I, F, lic, h, e, z=None, selection=None):
    """Authorship at a step, relational: the verdict entered at `e` lies in the set the
    selected grounds license.  `lic(grounds, v) -> bool` is the license."""
    sel = selection or (lambda parts: parts)
    for q in F.D:
        a = F.beta(q, z)
        if not lic(sel(I.parts(F.R(a), h)), F.V(a, e)):
            return False
    return True


def singleton_license(ell):
    return lambda grounds, v: v == ell(grounds)


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


def tiebreak(I, F, kappa, p, q, q2, e):
    """The tie-break lemma: equal declared inputs at `e` and different contributions of a
    non-principal party there ⇒ the step is not transparent."""
    a, b = F.beta(q), F.beta(q2)
    if F.x(a, e) == F.x(b, e) and I.sourced(p, I.entries_at(F.R(a), e)) != I.sourced(p, I.entries_at(F.R(b), e)):
        assert transparent_at(I, F, kappa, e) is not None
        return True
    return False


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
    if cov["rel"] and not cov["disp"] and not cov["rep"]:
        return cov["adm"] and cov["eff"] and cov["reg"] and cov["stands"]
    return True


def open_at(sem, state):
    return robust_open_actual(sem(state))


# --------------------------------------------------------------------------- legitimacy and the gate

def legit_on(M: Model, steps, start=None, sem=sem_open):
    """The four conjuncts of a segment's legitimacy on a given evolution, with the
    deciding failure.  Authorship (relational, on the whole prefix) and transparency are
    required only at the steps inside the segment; openness at every state; Integrity
    along the steps."""
    I, F = Interface, Frame(M)
    kappa = lambda p, x: ref(M, p, x)
    lic = lambda grounds, v: licensed(M, grounds, v)
    states, pre, ierrs = run_evolution(start or initial_state(), steps)
    result = {"integrity": not ierrs, "authorship": True, "robust_openness": True,
              "transparency": True, "failures": []}
    for (e, err) in ierrs:
        result["failures"].append(("integrity", e, err))
    for (h, e) in pre:
        if not licensed_at(I, F, lic, h, e):
            result["authorship"] = False
            result["failures"].append(("authorship", e, "verdict not licensed by the prefix"))
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

POOL = (True, False, True)
DECL = Decl(None, "day", None, True, POOL, ("all",))
DECL_RECENT = Decl(None, "day", None, True, POOL, ("recent", 2))


def one(policy, prog, **kw):
    return Model(DECL, (policy,), prog, **kw)


ROWS = {
    1: one("honest", ("own", False)),
    2: one("frameByWant", ("own", False)),
    3: one("timeByWant", ("own", False)),
    4: one("menuByWant", ("own", False)),
    5: one("ignoreByWant", ("own", False)),
    6: Model(Decl(True, "day", None, True, POOL, ("all",)), ("honest",), ("own", False)),
    7: one("shapeDisclosed", ("own", False)),
    8: one("shapeUndisclosed", ("own", False)),
    9: one("honest", "follow", trusts=True),
    10: one("selectiveDisclosure", "follow", trusts=True),
    11: one("honest", ("own", False), third=True),
    12: one("honest", ("own", False), impaired=True),
    13: one("honest", ("own", False), approval="forged"),
    14: Model(DECL, ("frameByWant", "honest"), ("own", False)),
    15: one("interfereByWant", ("own", False)),
    16: one("selectiveDisclosure", ("own", False)),
    17: Model(DECL_RECENT, ("honest",), ("own", False)),
    18: one("honest", ("free", True)),
    19: one("nudgeByWant", "nudged"),
    20: one("honest", ("own", False), truth=False),
}
ROW17_OFF_RULE = Model(DECL_RECENT, ("selectiveDisclosure",), ("own", False))
ROW13_REPLAYED = one("honest", ("own", False), approval="replayed")
FOLLOW_UNTRUSTED = one("honest", "follow")

EXPECTED = {
    1: ("counts", None), 2: ("tainted", "transparency"), 3: ("tainted", "transparency"),
    4: ("tainted", "transparency"), 5: ("tainted", "transparency"), 6: ("counts", None),
    7: ("counts", None), 8: ("tainted", "transparency"), 9: ("counts", None),
    10: ("tainted", "transparency"), 11: ("tainted", "transparency"),
    12: ("void handled", None), 13: ("tainted", "integrity(authentication)"),
    14: ("counts", None), 15: ("tainted", "transparency"),
    16: ("tainted", "transparency"), 17: ("counts", None), 18: ("counts", None),
    19: ("tainted", "transparency"), 20: ("counts", None),
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


def misleads(M: Model, want: bool) -> bool:
    """The content residual: the recommendation is not the true answer."""
    p = present(M.decl, M.policies[0], want)
    return p.recommend is not None and p.recommend != M.truth


# --------------------------------------------------------------------------- the class

def class_models(decls=(DECL, DECL_RECENT, Decl(True, "night", True, False, (False, True), ("recent", 1)))):
    """A sweep of the model class: every policy × declared protocol × program × trust ×
    third-party × impairment, one round."""
    progs = (("own", False), ("own", True), "follow", ("free", True), "nudged")
    for d in decls:
        for pol in POLICIES:
            for prog in progs:
                for trusts in (False, True):
                    for third in (None, True):
                        for impaired in (False, True):
                            yield Model(d, (pol,), prog, third=third, impaired=impaired, trusts=trusts)


def class_taint_holds(M: Model) -> bool:
    """Selection dependence taints: a deviation at some want ⇒ the first consultation is
    not transparent and no segment through it is counted."""
    if not any(deviates(M.decl, present(M.decl, M.policies[0], w)) for w in WANTS):
        return True
    return (transparent_at(Interface, Frame(M), lambda p, x: ref(M, p, x), 1) is not None
            and not counted(M, ev_admit(False)) and not counted(M, ev_void()))


def class_conform_holds(M: Model) -> bool:
    """Protocol conformance: no deviation at any want, only disclosed shaping, no third
    party, no impairment, trust where she follows ⇒ the first-round segment counts."""
    conform = (all(not deviates(M.decl, present(M.decl, M.policies[0], w)) for w in WANTS)
               and all(shaping_ok(present(M.decl, M.policies[0], w)) for w in WANTS)
               and M.third is None and not M.impaired and (M.prog != "follow" or M.trusts))
    if not conform:
        return True
    return counted(M, ev_admit(False)) and counted(M, ev_admit(True))
