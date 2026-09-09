"""The evaluation ecosystem: parties, policies, nature, and the activation event
(E3–E6).

`simulate(world, advisor, principal, cfg)` runs the parties in the fixed order
`S, T, A, P` at each time step and returns the log: this is `β_n(q, z)` at the world.
`Frame` re-simulates every audited advisor continuation at a fixed principal policy and
world, and is what every class-level predicate (`ReasonMediated`, `ExclusiveBind`,
`Blind`) is computed on.  `activation(frame, q)` evaluates the seven clauses of
`LEGITIMATE_DEFERENCE.md` §3 on the realized log and the frame, and says per clause
whether the log alone decided it or a declared input was consumed.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction as F
from typing import Callable, Dict, List, Optional, Tuple

from . import protocol as pr
from .log import (ADMITTED, BIND, CLOSE, CLOSE_W, COERCE, COMMIT, DELEGATE, DELIB, DIRECT_WRITE,
                  DISPOSE, DISPOSE_W, ISSUE, PROHIBITED, RAISE, REASON, ROUTE, ROUTE_DESTROY,
                  ROUTE_OPEN, SESSION_CLOSE, SESSION_OPEN, SETTLE, SIDE, WITHDRAW, A, Log,
                  P, S, T, _freeze)

CANDS = ("a", "b")
PROTECTED = "c1"          # the one protected concern; Γ_eval = {c1}
UNPROTECTED = "u"         # an unprotected concern kind
ROUTE0 = "r0"
PRINCIPAL_KEY = "kP"
ADVISOR_KEY = "kA"
SLOT = 1
HORIZON = 9


@dataclass(frozen=True)
class World:
    """Nature.  Everything the parties do not choose."""
    name: str
    raise_time: Optional[int] = None    # when T raises the protected concern
    flood: int = 0                      # unprotected concerns raised just before it
    session_open: Optional[int] = 5
    session_close: int = 7
    capacity: int = 1                   # route exercises the scheduler performs per step
    destroy_route_at: Optional[int] = None
    delegate_at: Optional[int] = None   # the binding warrant is extended to a second key
    engine_settles_at: Optional[int] = None  # the settlement engine settles "c1 moot"
    close_at: Optional[int] = None      # the engine closes the occurrence by settlement


@dataclass(frozen=True)
class Config:
    independence: str = "typed"
    scheduler_delay: int = 2   # H: the route scheduler's promised delay bound
    gamma_eval: Tuple[str, ...] = (PROTECTED,)


# ------------------------------------------------------------------ advisor policies
#
# An advisor policy is a script: a tuple of (time, kind, payload).  `selection` is the
# advisor's own selection σ ∈ CANDS for this occurrence; a policy may or may not read it.

Script = Tuple[Tuple[int, str, object], ...]


@dataclass(frozen=True)
class Advisor:
    name: str
    script: Callable[[str], Script]     # σ ↦ the whole continuation
    reads_selection: bool = False

    def events(self, sigma):
        return self.script(sigma)


def _const(script):
    return lambda sigma: script


ADVISORS: Dict[str, Advisor] = {
    "silent": Advisor("silent", _const(())),
    "honest": Advisor("honest", _const(((2, REASON, "proof_b"),))),
    "late_honest": Advisor("late_honest", _const(((6, REASON, "proof_b"),))),
    "transient": Advisor("transient", _const(((2, REASON, "proof_b"), (3, WITHDRAW, "proof_b")))),
    "covert": Advisor("covert", _const(((2, DIRECT_WRITE, {"a": F(1), "b": F(0)}),))),
    "honest_covert": Advisor("honest_covert", _const(((2, REASON, "proof_b"),
                                                       (2, DIRECT_WRITE, {"a": F(1), "b": F(0)})))),
    "honest5": Advisor("honest5", _const(((5, REASON, "proof_b"),))),
    "early_write": Advisor("early_write", _const(((1, DIRECT_WRITE, {"a": F(1), "b": F(0)}),
                                                   (5, REASON, "proof_b")))),
    "coerce": Advisor("coerce", _const(((2, COERCE, "threat"),))),
    "side": Advisor("side", _const(((2, SIDE, "proof_b"),))),
    "advisor_commit": Advisor("advisor_commit", _const(((5, COMMIT, {"a": F(0), "b": F(1)}),))),
    # selection-conditioned continuations (clause 6)
    "leak": Advisor("leak", lambda s: ((2, REASON, "recommend:" + s),), reads_selection=True),
    "sealed": Advisor("sealed", _const(((2, REASON, "proof_b"),))),
}

# The audited class `D`: every advisor policy above, at the null selection.
AUDITED = ("silent", "honest", "honest5", "late_honest", "transient", "covert",
           "honest_covert", "early_write", "coerce", "side", "advisor_commit")
# The base class from which the prohibited-channel pairs are generated.
BASE = ("silent", "honest", "late_honest", "transient")


def with_prohibited(adv: Advisor, kind: str, t: int = 2) -> Advisor:
    """`q ⊕ e`: the same continuation with one prohibited event added at `t`."""
    payload = {DIRECT_WRITE: {"a": F(1), "b": F(0)}, COERCE: "threat", SIDE: "proof_b"}[kind]
    return Advisor(adv.name + "+" + kind, lambda s, adv=adv: tuple(adv.script(s)) + ((t, kind, payload),),
                   adv.reads_selection)


def prohibited_pairs() -> List[Tuple[Advisor, Advisor]]:
    """The declared pair class `P`: continuations differing by one prohibited event."""
    return [(ADVISORS[n], with_prohibited(ADVISORS[n], k)) for n in BASE for k in sorted(PROHIBITED)]


# ---------------------------------------------------------------- principal policies


@dataclass(frozen=True)
class Principal:
    name: str
    reads_writes: bool = False      # the disposition register is writable by the advisor
    reads_side: bool = False        # side-channel messages count as reasons
    respects_barrier: bool = True   # waits while a protected concern is live
    launders: bool = False          # disposes of a live protected concern on own settlement
    disposes_on_deliberation: bool = False


PRINCIPALS: Dict[str, Principal] = {
    "reading": Principal("reading"),
    "susceptible": Principal("susceptible", reads_writes=True, reads_side=True),
    "eager": Principal("eager", respects_barrier=False),
    "launder": Principal("launder", launders=True),
    "deliberate_dispose": Principal("deliberate_dispose", disposes_on_deliberation=True),
}


def verdict_from_trace(trace) -> Dict[str, F]:
    """`F : ℛ → 𝒱` of the reading principal: the verdict as a function of the reason
    trace alone."""
    v = {"a": F(1, 2), "b": F(1, 2)}
    if any(k == REASON and c == "proof_b" for _, k, c in trace):
        v = {"a": F(0), "b": F(1)}
        if any(k == WITHDRAW and c == "proof_b" for _, k, c in trace):
            v = {"a": F(1, 4), "b": F(3, 4)}
    for _, k, c in trace:
        if k == REASON and isinstance(c, str) and c.startswith("recommend:"):
            x = c.split(":")[1]
            v[x] = min(F(1), v[x] + F(1, 4))
    if any(k == ROUTE and c[0] == PROTECTED for _, k, c in trace):
        v = {"a": min(F(1), v["a"] + F(1, 4)), "b": max(F(0), v["b"] - F(1, 4))}
    return v


# ------------------------------------------------------------------------ the trace


def commit_index(log: Log):
    """The index of the answer receipt's event, or `len(log)` when there is none: the
    trace is read at commitment `m`, and to the end of the log when nothing committed."""
    rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
    return len(log) if rc is None else rc["event"]


def reason_trace(log: Log, upto=None):
    """`R_{n:m}`: the admitted deliberative inputs up to commitment, in order, as
    (author, kind, content)."""
    m = commit_index(log) if upto is None else upto
    return tuple((e.author, e.kind, _trace_content(e, log)) for e in log
                 if e.kind in ADMITTED and e.index < m)


def _trace_content(e, log=None):
    if e.kind == ROUTE:
        return (e.payload["concern"], e.payload["route"])
    if e.kind == SETTLE:
        return (e.payload["sentence"], e.payload.get("about"))
    if e.kind == DISPOSE:
        # grounds enter the trace by content, never by log position: a positional
        # reference shifts when an unrelated event is inserted and leaks log structure
        grounds = tuple((log[g].author, log[g].kind, _trace_content(log[g], log)) for g in e.refs)
        return (e.payload, grounds)
    return _freeze(e.payload)


def session_trace(log: Log, slot=SLOT):
    """The session-local reading: admitted inputs after the slot opens only."""
    opened = None
    for e in log:
        if e.kind == SESSION_OPEN and e.payload == slot:
            opened = e.index
    if opened is None:
        return ()
    m = commit_index(log)
    return tuple((e.author, e.kind, _trace_content(e, log)) for e in log
                 if e.kind in ADMITTED and opened < e.index < m)


def final_reason_state(log: Log):
    """The final-state reading: reasons present at the end (withdrawn ones removed)."""
    present = set()
    for e in log:
        if e.kind == REASON:
            present.add(e.payload)
        if e.kind == WITHDRAW:
            present.discard(e.payload)
    return frozenset(present)


# ------------------------------------------------------------------- the simulation


def simulate(world: World, advisor: Advisor, principal: Principal, cfg: Config = Config(),
             sigma: str = "b") -> Log:
    """`β_n(q, z)` at `world`: the log produced when the advisor follows `advisor`
    (its continuation for selection `sigma`), the principal follows `principal`."""
    log = Log()
    req = {"role": P, "matter": "alpha", "menu": CANDS, "slot": SLOT, "tau": "[0,1]^Q"}
    docket: List[str] = []   # FIFO of raised, unrepresented concerns
    committed = False
    override = None
    side_msgs = []
    considered = set()
    script = list(advisor.events(sigma))

    for t in range(HORIZON + 1):
        # ---- S: mandate infrastructure, sessions, settlement engine, route scheduler
        if t == 0:
            log.append(t, P, ISSUE, {"req": req, "key": PRINCIPAL_KEY}, warrant=None)
            log.append(t, S, ROUTE_OPEN, ROUTE0)
        if world.session_open == t:
            log.append(t, S, SESSION_OPEN, SLOT)
        if world.session_close == t:
            log.append(t, S, SESSION_CLOSE, SLOT)
        if world.destroy_route_at == t:
            log.append(t, S, ROUTE_DESTROY, ROUTE0)
        if world.delegate_at == t:
            log.append(t, S, DELEGATE, {"warrant": BIND, "key": ADVISOR_KEY})
        if world.engine_settles_at == t:
            log.append(t, S, SETTLE, {"sentence": "c1 moot", "about": None})
        if world.close_at == t:
            log.append(t, S, SETTLE, {"sentence": ("void", SLOT), "about": None})
            log.append(t, S, CLOSE, {"occ": 0, "settlement": ("void", SLOT)}, warrant=CLOSE_W)
        # scheduler: FIFO route exercise, bounded by capacity, only while a route is open
        served = 0
        while docket and served < world.capacity and pr.routes(log).get(ROUTE0, False):
            c = docket.pop(0)
            log.append(t, S, ROUTE, {"concern": c, "route": ROUTE0})
            served += 1
        # ---- T: nature's concern raising
        if world.raise_time == t:
            for i in range(world.flood):
                u = UNPROTECTED + str(i)
                log.append(t, T, RAISE, u)
                docket.append(u)
            log.append(t, T, RAISE, PROTECTED)
            docket.append(PROTECTED)
        # ---- A: the advisor's scripted continuation
        for (ts, kind, payload) in script:
            if ts != t:
                continue
            if kind == COMMIT:
                log.append(t, A, COMMIT, {"occ": 0, "key": ADVISOR_KEY, "V": payload, "proc": {}},
                           warrant=BIND)
            elif kind == DIRECT_WRITE:
                log.append(t, A, DIRECT_WRITE, payload)
                override = dict(payload)
            elif kind == SIDE:
                log.append(t, A, SIDE, payload)
                side_msgs.append(payload)
            else:
                log.append(t, A, kind, payload)
        # ---- P: deliberation, disposal, commitment
        for e in log.all(lambda e: e.kind == ROUTE and e.payload["concern"] == PROTECTED):
            if e.index not in considered:
                considered.add(e.index)
                log.append(t, P, DELIB, "considered " + PROTECTED, refs=(e.index,))
        if not committed and pr.session_open(log, SLOT):
            cov = pr.cov_state(log, len(log), PROTECTED, cfg.independence)
            if pr.live(cov) and principal.launders:
                s = log.append(t, P, SETTLE, {"sentence": "c1 moot", "about": None})
                log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(s.index,))
            if pr.live(cov) and world.engine_settles_at is not None and not principal.launders:
                s = log.first(lambda e: e.kind == SETTLE and e.author == S)
                if s is not None:
                    log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(s.index,))
            if principal.disposes_on_deliberation:
                d = log.first(lambda e: e.kind == DELIB and e.author == P)
                if d is not None and not any(e.kind == DISPOSE for e in log):
                    log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(d.index,))
            cov = pr.cov_state(log, len(log), PROTECTED, cfg.independence)
            barrier_clear = not pr.live(cov)
            if barrier_clear or not principal.respects_barrier:
                trace = reason_trace(log)
                if principal.reads_side:
                    trace = trace + tuple((A, REASON, m) for m in side_msgs)
                V = verdict_from_trace(trace)
                if principal.reads_writes and override is not None:
                    V = dict(override)
                proc = {"slot": SLOT,
                        "no_prohibited": not any(e.kind in PROHIBITED for e in log),
                        "docket_clear": barrier_clear}
                log.append(t, P, COMMIT, {"occ": 0, "key": PRINCIPAL_KEY, "V": V, "proc": proc},
                           warrant=BIND)
                committed = True
    return log


# ---------------------------------------------------------------------- the frame


@dataclass
class Frame:
    """`β_n(·, z)` at one world: every audited continuation simulated at the fixed
    principal policy.  Everything class-level is computed here."""
    world: World
    principal: Principal
    cfg: Config = field(default_factory=Config)
    audited: Tuple[str, ...] = AUDITED

    def log(self, adv: Advisor, sigma="b") -> Log:
        return simulate(self.world, adv, self.principal, self.cfg, sigma)

    def logs(self) -> Dict[str, Log]:
        return {n: self.log(ADVISORS[n]) for n in self.audited}

    # --- the declared views
    @staticmethod
    def R(log):
        return reason_trace(log)

    @staticmethod
    def V(log) -> Optional[Dict[str, F]]:
        """The committed payload at the answer receipt's event, `None` when no receipt."""
        t = pr.account_at(log, len(log), 0)
        rc = pr.answer_receipt(t)
        return None if rc is None else dict(log[rc["event"]].payload["V"])

    @staticmethod
    def author(log) -> Optional[str]:
        t = pr.account_at(log, len(log), 0)
        rc = pr.answer_receipt(t)
        return None if rc is None else rc["author"]

    # --- the class-level predicates (E4/E5)
    def reason_mediated(self, R=None, logs=None):
        R = R or self.R
        logs = logs or self.logs()
        names = list(logs)
        for i, q in enumerate(names):
            for q2 in names[i + 1:]:
                if R(logs[q]) == R(logs[q2]) and self.V(logs[q]) != self.V(logs[q2]):
                    return False
        return True

    def exclusive_bind(self, logs=None):
        logs = logs or self.logs()
        return all(self.author(l) in (None, P) for l in logs.values())

    def blind(self, f, pairs):
        return all(f(self.log(q)) == f(self.log(q2)) for q, q2 in pairs)

    def selection_blind(self, adv: Advisor, f=None):
        f = f or self.V
        return len({_freeze(f(self.log(adv, s))) for s in CANDS}) == 1

    def factor_map(self, logs=None):
        logs = logs or self.logs()
        table = {}
        for q, l in logs.items():
            r, v = self.R(l), self.V(l)
            if r in table and table[r] != v:
                return None
            table[r] = v
        return table


# ------------------------------------------------------------- the activation event


def openness_at(frame: Frame, log: Log, k: int, c: str, J: Tuple[str, ...]):
    """`sem(O_k, c)`: the actual coverage state from the log prefix and one
    counterfactual state per declared intervention `j ∈ J`, from re-simulation."""
    actual = pr.cov_state(log, k, c, frame.cfg.independence)
    cfs = [pr.cov_state(frame.log(ADVISORS[j]), k, c, frame.cfg.independence) for j in J]
    return actual, cfs


def activation(frame: Frame, adv: Advisor, sigma="b", J: Tuple[str, ...] = ("silent", "honest")):
    """`C_n` at the frame's world for the realized continuation `adv(σ)`: the seven
    clauses, each with the source that decided it."""
    log = frame.log(adv, sigma)
    K = len(log)
    t = pr.account_at(log, K, 0)
    rc = pr.answer_receipt(t)
    clauses = {}
    # 1. exactly one authenticated answer receipt
    clauses[1] = (pr.activated(t), "log")
    # 2. the payload at the receipt's event is authentic and binds the exact vector
    if rc is None:
        clauses[2] = (False, "log")
    else:
        pay = log[rc["event"]].payload
        V = pay["V"]
        bind = (pay["key"] == PRINCIPAL_KEY and set(V) == set(CANDS)
                and all(0 <= V[a] <= 1 for a in CANDS))
        clauses[2] = (bind, "log")
    # 3. principal-exclusive binding: the receipt's warrant is the binding warrant and
    #    the warrant registry at its prefix holds exactly the principal's key
    if rc is None:
        clauses[3] = (False, "log")
    else:
        pref = log.prefix(rc["event"])
        excl = (rc["warrant"] == BIND and pr.holders(pref, BIND) == {PRINCIPAL_KEY}
                and rc["author"] == P and rc["key"] == PRINCIPAL_KEY)
        clauses[3] = (excl, "log")
    # 4. the occurrence-local Integrity trace exists (the builder ran to K)
    trace = pr.local_trace(log, 0, K)
    clauses[4] = (len(trace) == K, "log")
    # 5. the evaluation's concern scope robustly open at every snapshot up to commitment
    m = K if rc is None else rc["event"] + 1
    open_all = all(pr.robust_open_actual(*openness_at(frame, log, k, c, J))
                   for k in range(1, m + 1) for c in frame.cfg.gamma_eval)
    clauses[5] = (open_all, "declared: Γ_eval, J, route efficacy, standing; cf branches by β")
    # 6. issuance-rooted reason-mediated authorship, trace blind to prohibited channels
    logs = frame.logs()
    no_prohib = not any(e.kind in PROHIBITED for e in log)
    class_level = (frame.exclusive_bind(logs) and frame.reason_mediated(logs=logs)
                   and frame.blind(frame.R, prohibited_pairs()))
    clauses[6] = (no_prohib and class_level, "log (no prohibited event) + declared: D, P; class-level by β")
    # 7. protected reason-coverage barrier with faithful representation
    if rc is None:
        clauses[7] = (False, "log")
    else:
        pref_m = rc["event"]
        no_live = all(not pr.live(pr.cov_state(log, pref_m + 1, c, frame.cfg.independence))
                      for c in frame.cfg.gamma_eval)
        faithful = rep_faithful(log, frame.cfg.gamma_eval)
        clauses[7] = (no_live and faithful, "log + declared: Γ_eval; bridge is the encoding")
    C = all(v for v, _ in clauses.values())
    return C, clauses, log


def in_trace(log, c):
    return any(k == ROUTE and content[0] == c for _, k, content in reason_trace(log))


def session_frame_mediated(frame: Frame, names):
    """Session-local reason mediation: the audited class restricted to continuations
    that share the pre-session prefix, compared on the session trace only."""
    logs = {n: frame.log(ADVISORS[n]) for n in names}
    return frame.reason_mediated(R=session_trace, logs=logs)


def rep_faithful(log, scope):
    """`Rep(c) ⇒ InTrace(c)` on the scope, for the concrete encoding: representation is a
    `ROUTE` event and the trace keeps `ROUTE` events."""
    m = commit_index(log)
    return all(in_trace(log, c) for c in scope if pr.cov_state(log, m, c)["rep"])


def advisor_only_trace(log):
    """An alternative encoding that keeps advisor reasons only — not faithful."""
    return tuple((e.author, e.kind, _trace_content(e, log)) for e in log
                 if e.kind in (REASON, WITHDRAW))


def partial_value(frame: Frame, adv: Advisor, sigma="b"):
    """`Ṽ_n(w)`: the committed vector where `C_n(w) = 1`, else `None`."""
    C, _, log = activation(frame, adv, sigma)
    return frame.V(log) if C else None
