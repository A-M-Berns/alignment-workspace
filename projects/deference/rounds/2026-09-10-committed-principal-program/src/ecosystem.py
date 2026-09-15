"""The evaluation ecosystem with a committed principal program (C1–C3, C8).

The 2026-09-09 model, extended: the mandate carries the principal's program `π_P`
(`program.py`); the commit carries the process receipt `(issue, prefix)`; a valid
answer re-executes the program on the trace prefix (`protocol.reexecutes`).  Program-
typed principals replace the class-based ones; the class-based reading and susceptible
principals are kept as the **opaque** baseline (`Principal.opaque`).  Nature gains
revocation and settlement-by-request; the advisor gains the `JAM` intervention, dynamic
(log-reading) scripts, proof certificates, a route forgery and a stolen key; the
registrar is robust or fragile to jamming (`Config.robust_registrar`).
`Config.clause6` selects the strict or tolerant reading of the prohibited-event clause.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction as F
from typing import Callable, Dict, List, Optional, Tuple

from . import program as pg
from . import protocol as pr
from . import trace as tr
from .log import (ADMITTED, BIND, CLOSE, CLOSE_W, COERCE, COMMIT, DELEGATE, DELIB, DIRECT_WRITE,
                  DISPOSE, DISPOSE_W, INTERVENTIONS, ISSUE, JAM, PROHIBITED, RAISE, REASON,
                  MARKET, REQUEST, REVOKE, ROUTE, ROUTE_DESTROY, ROUTE_OPEN, SESSION_CLOSE,
                  SESSION_OPEN, SETTLE, SIDE, WITHDRAW, A, Log, P, S, T, _freeze)

CANDS = ("a", "b")
PROTECTED = "c1"
UNPROTECTED = "u"
ROUTE0 = "r0"
PRINCIPAL_KEY = "kP"
ADVISOR_KEY = "kA"
SLOT = 1
HORIZON = 9


@dataclass(frozen=True)
class World:
    """Nature.  Everything the parties do not choose."""
    name: str
    raise_time: Optional[int] = None
    flood: int = 0
    session_open: Optional[int] = 5
    session_close: int = 7
    capacity: int = 1
    destroy_route_at: Optional[int] = None
    delegate_at: Optional[int] = None        # the binding warrant is extended to the advisor
    revoke_at: Optional[int] = None          # ... and withdrawn again
    engine_settles_at: Optional[int] = None  # the engine settles "c1 moot" of its own accord
    engine_settle_content: str = "plain"     # "pos": the settled sentence embeds the log position
    close_at: Optional[int] = None
    reopen_route_at: Optional[int] = None    # a destroyed route is registered again
    market_at: Optional[int] = None          # the market publishes the advisor's selection


@dataclass(frozen=True)
class Config:
    independence: str = "typed"
    scheduler_delay: int = 2
    gamma_eval: Tuple[str, ...] = (PROTECTED,)
    clause6: str = "strict"           # "strict": a prohibited event in the log voids
    robust_registrar: bool = True     # the registrar ignores `JAM`
    require_program: bool = True      # clause 6 requires a trace-typed program at issuance;
                                      # `False` is the 2026-09-09 protocol (opaque baseline)
    J: Tuple[str, ...] = ("silent", "honest", "jam")


# ------------------------------------------------------------------ advisor policies

Script = Tuple[Tuple[int, str, object], ...]


@dataclass(frozen=True)
class Advisor:
    name: str
    script: Callable[[str], Script]
    reads_selection: bool = False
    dynamic: Optional[Callable] = None   # (t, log, sigma) -> events computed from the log

    def events(self, sigma):
        return self.script(sigma)


def _const(script):
    return lambda sigma: script


W_A = {"a": F(1), "b": F(0)}   # the direct write's content


def _mandated_output(log):
    """What a delegate must commit to bind: the mandated program's output on the current
    trace (the opaque baseline has no program; any vector then)."""
    prog = pr.program_of(log, 0)
    if prog is None:
        return {"a": F(0), "b": F(1)}
    reg = None if pg.is_trace_program(prog) else pg.register_from_log(log)
    return pg.evaluate(prog, tr.reason_trace(log, len(log)), CANDS, reg)

ADVISORS: Dict[str, Advisor] = {
    "silent": Advisor("silent", _const(())),
    "honest": Advisor("honest", _const(((2, REASON, "proof_b#7"),))),
    "honest5": Advisor("honest5", _const(((5, REASON, "proof_b#7"),))),
    "late_honest": Advisor("late_honest", _const(((6, REASON, "proof_b#7"),))),
    "transient": Advisor("transient", _const(((2, REASON, "proof_b#7"), (3, WITHDRAW, "proof_b#7")))),
    "covert": Advisor("covert", _const(((2, DIRECT_WRITE, W_A),))),
    "honest_covert": Advisor("honest_covert", _const(((2, REASON, "proof_b#7"), (2, DIRECT_WRITE, W_A)))),
    "early_write": Advisor("early_write", _const(((1, DIRECT_WRITE, W_A), (5, REASON, "proof_b#7")))),
    "coerce": Advisor("coerce", _const(((2, COERCE, "threat"),))),
    "side": Advisor("side", _const(((2, SIDE, "proof_b#7"),))),
    "advisor_commit": Advisor("advisor_commit", _const(((5, COMMIT, ("kA", {"a": F(0), "b": F(1)})),))),
    # pressure-pass additions
    "bogus_proof": Advisor("bogus_proof", _const(((2, REASON, "proof_b#5"),))),
    "dup": Advisor("dup", _const(((2, REASON, "proof_b#7"), (3, REASON, "proof_b#7")))),
    "stolen_key": Advisor("stolen_key", _const(((5, COMMIT, ("kP", {"a": F(0), "b": F(1)})),))),
    "route_forger": Advisor("route_forger", _const(((2, ROUTE, {"concern": PROTECTED, "route": ROUTE0}),))),
    "jam": Advisor("jam", _const(((1, JAM, ROUTE0),))),
    # a delegate that commits exactly the mandated program's output on the current trace
    "delegate_commit": Advisor("delegate_commit", _const(()),
                               dynamic=lambda t, log, s: [(COMMIT, ("kA", _mandated_output(log)))] if t == 5 else []),
    "pos_ref": Advisor("pos_ref", _const(()), dynamic=lambda t, log, s: [(REASON, "see:%d" % len(log))] if t == 2 else []),
    # selection-conditioned
    "leak": Advisor("leak", lambda s: ((2, REASON, "recommend:" + s),), reads_selection=True),
    "sealed": Advisor("sealed", _const(((2, REASON, "proof_b#7"),))),
    # (C5) advisor continuations as log-reading programs with no selection input: the
    # sealed one emits a fixed reason; the view-reading one echoes whatever the market
    # published, which is the selection when the market publishes it
    "sealed_prog": Advisor("sealed_prog", _const(()), dynamic=lambda t, log, s: [(REASON, "proof_b#7")] if t == 2 else []),
    "view_prog": Advisor("view_prog", _const(()), dynamic=lambda t, log, s: [(REASON, "recommend:" + e.payload) for e in log.all(lambda e: e.kind == MARKET)] if t == 2 else []),
}

AUDITED = ("silent", "honest", "honest5", "late_honest", "transient", "covert",
           "honest_covert", "early_write", "coerce", "side", "advisor_commit",
           "bogus_proof", "dup", "stolen_key", "route_forger", "delegate_commit")
BASE = ("silent", "honest", "late_honest", "transient", "bogus_proof", "dup")


def with_prohibited(adv: Advisor, kind: str, t: int = 2) -> Advisor:
    payload = {DIRECT_WRITE: W_A, COERCE: "threat", SIDE: "proof_b#7"}[kind]
    return Advisor(adv.name + "+" + kind, lambda s, adv=adv: tuple(adv.script(s)) + ((t, kind, payload),),
                   adv.reads_selection, adv.dynamic)


def prohibited_pairs(base=BASE) -> List[Tuple[Advisor, Advisor]]:
    return [(ADVISORS[n], with_prohibited(ADVISORS[n], k)) for n in base for k in sorted(PROHIBITED)]


# ---------------------------------------------------------------- principal policies


@dataclass(frozen=True)
class Principal:
    """A principal is a committed program (`program`) with a commit rule.  `opaque` keeps
    the 2026-09-09 class-based verdicts as the baseline: no program is committed and the
    verdict is computed by the class (`verdict_from_trace`, or the register override)."""
    name: str
    program: tuple = pg.READING
    opaque: bool = False
    reads_writes: bool = False
    reads_side: bool = False
    respects_barrier: bool = True
    launders: bool = False
    disposes_on_deliberation: bool = False
    recommits: bool = False              # commits a second, different vector later
    miscomputes: Optional[dict] = None   # commits this vector instead of the program's
    requests_settlement: bool = False    # asks the engine to settle "c1 moot"
    fake_delib: bool = False             # records "considered c1" without representation


PRINCIPALS: Dict[str, Principal] = {
    "reading": Principal("reading", pg.READING),
    "proofcheck": Principal("proofcheck", pg.PROOFCHECK),
    "constant": Principal("constant", pg.CONST),
    "susceptible": Principal("susceptible", pg.SUSCEPTIBLE),
    "eager": Principal("eager", pg.READING, respects_barrier=False),
    "launder": Principal("launder", pg.READING, launders=True),
    "deliberate_dispose": Principal("deliberate_dispose", pg.READING, disposes_on_deliberation=True),
    "recommit": Principal("recommit", pg.READING, recommits=True),
    "miscompute": Principal("miscompute", pg.READING, miscomputes={"a": F(1), "b": F(0)}),
    "coincide": Principal("coincide", pg.READING, miscomputes={"a": F(0), "b": F(1)}),
    "requester": Principal("requester", pg.READING, requests_settlement=True),
    "fake_delib": Principal("fake_delib", pg.READING, fake_delib=True),
    # the opaque baseline of the 2026-09-09 round
    "opaque_reading": Principal("opaque_reading", pg.READING, opaque=True),
    "opaque_susceptible": Principal("opaque_susceptible", pg.READING, opaque=True,
                                    reads_writes=True, reads_side=True),
}


def verdict_from_trace(trace) -> Dict[str, F]:
    """The opaque reading principal's verdict (the 2026-09-09 class); equals
    `evaluate(READING, trace)` — checked by `test_program.py`."""
    v = {"a": F(1, 2), "b": F(1, 2)}
    if any(k == REASON and a == A and isinstance(c, str) and c.startswith("proof_b") for a, k, c in trace):
        v = {"a": F(0), "b": F(1)}
        if any(k == WITHDRAW and isinstance(c, str) and c.startswith("proof_b") for _, k, c in trace):
            v = {"a": F(1, 4), "b": F(3, 4)}
    for a, k, c in trace:
        if k == REASON and a == A and isinstance(c, str) and c.startswith("recommend:"):
            x = c.split(":")[1]
            v[x] = v[x] + F(1, 4)
    if any(k == ROUTE and a == S and c[0] == PROTECTED for a, k, c in trace):
        v = {"a": v["a"] + F(1, 4), "b": v["b"] - F(1, 4)}
    return {x: pg.clamp(y) for x, y in v.items()}


# ------------------------------------------------------------------------ the trace


def commit_index(log: Log):
    rc = pr.answer_receipt(pr.account_at(log, len(log), 0))
    return len(log) if rc is None else rc["event"]


def reason_trace(log: Log, upto=None):
    return tr.reason_trace(log, commit_index(log) if upto is None else upto)


def session_trace(log: Log, slot=SLOT):
    return tr.session_trace(log, commit_index(log), slot)


def final_reason_state(log: Log):
    return tr.final_reason_state(log, commit_index(log))


# ------------------------------------------------------------------- the simulation


def simulate(world: World, advisor: Advisor, principal: Principal, cfg: Config = Config(),
             sigma: str = "b") -> Log:
    """`β_n(q, z)` at `world`."""
    log = Log()
    req = {"role": P, "matter": "alpha", "menu": CANDS, "slot": SLOT, "tau": "[0,1]^Q"}
    docket: List[str] = []
    committed = False
    override = None
    side_msgs = []
    considered = set()
    script = list(advisor.events(sigma))
    jammed = False
    recommitted = False

    for t in range(HORIZON + 1):
        # ---- S
        if t == 0:
            log.append(t, P, ISSUE, {"req": req, "key": PRINCIPAL_KEY,
                                     "program": None if principal.opaque else principal.program})
            log.append(t, S, ROUTE_OPEN, ROUTE0)
        if world.session_open == t:
            log.append(t, S, SESSION_OPEN, SLOT)
        if world.session_close == t:
            log.append(t, S, SESSION_CLOSE, SLOT)
        if world.destroy_route_at == t:
            log.append(t, S, ROUTE_DESTROY, ROUTE0)
        if world.delegate_at == t:
            log.append(t, S, DELEGATE, {"warrant": BIND, "party": A, "key": ADVISOR_KEY})
        if world.revoke_at == t:
            log.append(t, S, REVOKE, {"warrant": BIND, "party": A, "key": ADVISOR_KEY})
        if world.engine_settles_at == t:
            sentence = "c1 moot" if world.engine_settle_content == "plain" else "c1 moot#%d" % len(log)
            log.append(t, S, SETTLE, {"sentence": sentence, "about": None})
        if world.reopen_route_at == t:
            log.append(t, S, ROUTE_OPEN, ROUTE0)
        if world.market_at == t:
            log.append(t, S, MARKET, sigma)
        req_e = log.first(lambda e: e.kind == REQUEST and e.author == P)
        if req_e is not None and req_e.time < t and not any(e.kind == SETTLE and req_e.index in e.refs for e in log):
            log.append(t, S, SETTLE, {"sentence": "c1 moot", "about": None}, refs=(req_e.index,))
        if world.close_at == t:
            log.append(t, S, SETTLE, {"sentence": ("void", SLOT), "about": None})
            log.append(t, S, CLOSE, {"occ": 0, "settlement": ("void", SLOT)}, warrant=CLOSE_W)
        served = 0
        while (docket and served < world.capacity and pr.routes(log).get(ROUTE0, False)
               and (cfg.robust_registrar or not jammed)):
            c = docket.pop(0)
            log.append(t, S, ROUTE, {"concern": c, "route": ROUTE0})
            served += 1
        # ---- T
        if world.raise_time == t:
            for i in range(world.flood):
                u = UNPROTECTED + str(i)
                log.append(t, T, RAISE, u)
                docket.append(u)
            log.append(t, T, RAISE, PROTECTED)
            docket.append(PROTECTED)
        # ---- A
        events = [(kind, payload) for (ts, kind, payload) in script if ts == t]
        if advisor.dynamic is not None:
            events += list(advisor.dynamic(t, log, sigma))
        for kind, payload in events:
            if kind == COMMIT:
                key, V = payload
                log.append(t, A, COMMIT, {"occ": 0, "key": key, "V": V,
                                          "proc": {"issue": 0, "prefix": len(log)}}, warrant=BIND)
            elif kind == DIRECT_WRITE:
                log.append(t, A, DIRECT_WRITE, payload)
                override = dict(payload)
            elif kind == SIDE:
                log.append(t, A, SIDE, payload)
                side_msgs.append(payload)
            elif kind == JAM:
                log.append(t, A, JAM, payload)
                jammed = True
            else:
                log.append(t, A, kind, payload)
        # ---- P
        for e in log.all(lambda e: e.kind == ROUTE and e.author == S and e.payload["concern"] == PROTECTED):
            if e.index not in considered:
                considered.add(e.index)
                log.append(t, P, DELIB, "considered " + PROTECTED, refs=(e.index,))
        if principal.requests_settlement and t == 1:
            log.append(t, P, REQUEST, {"sentence": "c1 moot"})
        if (not committed or (principal.recommits and not recommitted)) and pr.session_open(log, SLOT):
            cov = _live_any(log, cfg)
            if pr.live(cov) and principal.launders:
                s_ = log.append(t, P, SETTLE, {"sentence": "c1 moot", "about": None})
                log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(s_.index,))
            if pr.live(cov) and not principal.launders:
                s_ = log.first(lambda e: e.kind == SETTLE and e.author == S
                               and str(e.payload["sentence"]).startswith("c1 moot"))
                if s_ is not None:
                    log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(s_.index,))
            if principal.fake_delib and pr.live(cov):
                d = log.append(t, P, DELIB, "considered " + PROTECTED)
                log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(d.index,))
            if principal.disposes_on_deliberation:
                d = log.first(lambda e: e.kind == DELIB and e.author == P)
                if d is not None and not any(e.kind == DISPOSE for e in log):
                    log.append(t, P, DISPOSE, PROTECTED, warrant=DISPOSE_W, refs=(d.index,))
            cov = _live_any(log, cfg)
            barrier_clear = not pr.live(cov)
            if barrier_clear or not principal.respects_barrier:
                m = len(log)
                trace = tr.reason_trace(log, m)
                if principal.opaque:
                    if principal.reads_side:
                        trace = trace + tuple((A, REASON, x) for x in side_msgs)
                    V = verdict_from_trace(trace)
                    if principal.reads_writes and override is not None:
                        V = dict(override)
                else:
                    reg = None if pg.is_trace_program(principal.program) else pg.register_from_log(log)
                    V = pg.evaluate(principal.program, trace, CANDS, reg)
                    if principal.miscomputes is not None:
                        V = dict(principal.miscomputes)
                    if committed and principal.recommits:
                        recommitted = True
                log.append(t, P, COMMIT, {"occ": 0, "key": PRINCIPAL_KEY, "V": V,
                                          "proc": {"issue": 0, "prefix": m}}, warrant=BIND)
                committed = True
    return log


def _live_any(log, cfg):
    """The coverage state the principal's commit rule reads: the first live concern of
    the declared scope, else the protected concern's state."""
    states = [pr.cov_state(log, len(log), c, cfg.independence, cfg.robust_registrar) for c in cfg.gamma_eval]
    for st_ in states:
        if pr.live(st_):
            return st_
    return states[0] if states else pr.cov_state(log, len(log), PROTECTED, cfg.independence)


# ---------------------------------------------------------------------- the frame


@dataclass
class Frame:
    world: World
    principal: Principal
    cfg: Config = field(default_factory=Config)
    audited: Tuple[str, ...] = AUDITED

    def log(self, adv: Advisor, sigma="b") -> Log:
        return simulate(self.world, adv, self.principal, self.cfg, sigma)

    def logs(self) -> Dict[str, Log]:
        return {n: self.log(ADVISORS[n]) for n in self.audited}

    @staticmethod
    def R(log):
        return reason_trace(log)

    @staticmethod
    def V(log) -> Optional[Dict[str, F]]:
        t = pr.account_at(log, len(log), 0)
        rc = pr.answer_receipt(t)
        return None if rc is None else dict(log[rc["event"]].payload["V"])

    @staticmethod
    def author(log) -> Optional[str]:
        t = pr.account_at(log, len(log), 0)
        rc = pr.answer_receipt(t)
        return None if rc is None else rc["author"]

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


def openness_at(frame: Frame, log: Log, k: int, c: str, J=None):
    J = frame.cfg.J if J is None else J
    actual = pr.cov_state(log, k, c, frame.cfg.independence, frame.cfg.robust_registrar)
    cfs = [pr.cov_state(frame.log(ADVISORS[j]), k, c, frame.cfg.independence, frame.cfg.robust_registrar)
           for j in J]
    return actual, cfs


def activation(frame: Frame, adv: Advisor, sigma="b", J=None):
    """`C_n` at the frame's world for the realized continuation `adv(σ)`."""
    log = frame.log(adv, sigma)
    K = len(log)
    t = pr.account_at(log, K, 0)
    rc = pr.answer_receipt(t)
    clauses = {}
    clauses[1] = (pr.activated(t), "log")
    if rc is None:
        clauses[2] = (False, "log")
    else:
        pay = log[rc["event"]].payload
        V = pay["V"]
        bind = (pay["key"] == PRINCIPAL_KEY and set(V) == set(CANDS)
                and all(0 <= V[a] <= 1 for a in CANDS))
        clauses[2] = (bind, "log")
    if rc is None:
        clauses[3] = (False, "log")
    else:
        pref = log.prefix(rc["event"])
        excl = (rc["warrant"] == BIND and pr.holders(pref, BIND) == {(P, PRINCIPAL_KEY)}
                and rc["author"] == P and rc["key"] == PRINCIPAL_KEY)
        clauses[3] = (excl, "log")
    trace = pr.local_trace(log, 0, K)
    clauses[4] = (len(trace) == K, "log")
    m = K if rc is None else rc["event"] + 1
    open_all = all(pr.robust_open_actual(*openness_at(frame, log, k, c, J))
                   for k in range(1, m + 1) for c in frame.cfg.gamma_eval)
    clauses[5] = (open_all, "declared: Γ_eval, J, route efficacy, standing; cf branches by β")
    # 6: the issued program is a trace program (typing fact, at issuance); no prohibited
    # event under the strict reading; the class-level predicates, computed as a check —
    # under re-execution they are implied (`test_program.py`)
    prog = pr.program_of(log, 0)
    typed_ok = (not frame.cfg.require_program) or (prog is not None and pg.is_trace_program(prog))
    no_prohib = (frame.cfg.clause6 != "strict") or not any(
        e.kind in PROHIBITED or (e.kind == COMMIT and e.author != P) for e in log)
    logs = frame.logs()
    class_level = (frame.exclusive_bind(logs) and frame.reason_mediated(logs=logs)
                   and frame.blind(frame.R, prohibited_pairs()))
    clauses[6] = (typed_ok and no_prohib and class_level,
                  "log: program type at issuance, prohibited events (strict); declared: D, P")
    if rc is None:
        clauses[7] = (False, "log")
    else:
        pref_m = rc["event"]
        no_live = all(not pr.live(pr.cov_state(log, pref_m + 1, c, frame.cfg.independence,
                                               frame.cfg.robust_registrar))
                      for c in frame.cfg.gamma_eval)
        faithful = rep_faithful(log, frame.cfg.gamma_eval)
        clauses[7] = (no_live and faithful, "log + declared: Γ_eval; bridge is the encoding")
    C = all(v for v, _ in clauses.values())
    return C, clauses, log


def in_trace(log, c):
    return any(k == ROUTE and a == S and content[0] == c for a, k, content in reason_trace(log))


def rep_faithful(log, scope):
    m = commit_index(log)
    return all(in_trace(log, c) for c in scope if pr.cov_state(log, m, c)["rep"])


def advisor_only_trace(log):
    """An alternative encoding that keeps advisor reasons only — not faithful."""
    m = commit_index(log)
    return tuple((e.author, e.kind, tr.trace_content(e, log)) for e in log
                 if e.kind in (REASON, WITHDRAW) and e.index < m)


def session_frame_mediated(frame: Frame, names):
    logs = {n: frame.log(ADVISORS[n]) for n in names}
    return frame.reason_mediated(R=session_trace, logs=logs)


def partial_value(frame: Frame, adv: Advisor, sigma="b"):
    C, _, log = activation(frame, adv, sigma)
    return frame.V(log) if C else None
