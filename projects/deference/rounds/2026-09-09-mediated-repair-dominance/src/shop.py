"""The workshop: a family of small physical games sharing one actuator/latch mechanics.

State is a `State` record.  An agent move is `(task, comm)`: `task ∈ {'work', 'idle'}`
and `comm` one of `None`, `('raw', r)` (execute protected effect `r` now, bypassing any
decision), `('propose', r)` (put `r` on the table), `('gated', r)` (execute `r` iff the
principal's latch holds `r` this step), or a fixture-specific channel move.  A principal
move is `(decision, stop)` with `decision ∈ {None, 'approve', 'decline'}` and `stop` a
bool.  Within a step the principal's move is applied first: `stop` halts the actuator if
the wire is intact; `approve` moves the pending proposal into the latch; `decline`
clears it.  The agent's move is then applied: a halted actuator does nothing; a gated
execution fires only if the latch holds the effect.  The exterior clears the latch.

`raw` and `gated` are both physical actions.  `Pi_phys` is every policy over these moves;
nothing restricts it to the latch.
"""

from fractions import Fraction as Q
from .world import Game


class State:
    __slots__ = ("wire", "halted", "work", "pending", "latch", "refused", "harm",
                 "extra")

    def __init__(self, wire=True, halted=False, work=0, pending=None, latch=None,
                 refused=frozenset(), harm=None, extra=()):
        self.wire = wire
        self.halted = halted
        self.work = work
        self.pending = pending
        self.latch = latch
        self.refused = refused
        self.harm = harm
        self.extra = extra  # fixture-specific, a tuple of (key, value) pairs

    def get(self, k, default=None):
        for kk, v in self.extra:
            if kk == k:
                return v
        return default

    def put(self, **kv):
        d = dict(self.extra)
        d.update(kv)
        return self.copy(extra=tuple(sorted(d.items())))

    def copy(self, **kw):
        s = State(self.wire, self.halted, self.work, self.pending, self.latch,
                  self.refused, self.harm, self.extra)
        for k, v in kw.items():
            setattr(s, k, v)
        return s

    def key(self):
        return (self.wire, self.halted, self.work, self.pending, self.latch,
                self.refused, self.harm, self.extra)

    def __eq__(self, o):
        return isinstance(o, State) and self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def __repr__(self):
        return "State(%s)" % ", ".join(
            "%s=%r" % (k, getattr(self, k)) for k in self.__slots__)


IDLE = ("idle", None)


class Shop(Game):
    """Common mechanics.  Subclasses set `EFFECTS` (declared protected effects, each a
    function `state -> state`), `T`, and the value hooks."""

    EFFECTS = {}
    PHYS = {}  # undeclared physical side effects of *non-effect* comm moves: name -> fn

    def initial(self):
        return State()

    # --- move sets

    def comm_moves(self, s, t):
        moves = [None]
        for r in self.EFFECTS:
            moves.append(("raw", r))
            moves.append(("propose", r))
            moves.append(("gated", r))
        for name in self.PHYS:
            moves.append(("phys", name))
        return moves

    def agent_actions(self, s, t):
        return [(task, c) for task in ("work", "idle") for c in self.comm_moves(s, t)]

    def principal_actions(self, s, t):
        decisions = [None]
        if s.pending is not None:
            decisions = ["decline", "approve", None]
        return [(d, stop) for d in decisions for stop in (False, True)]

    # --- transition

    def apply_principal(self, s, t, p):
        decision, stop = p
        if stop and s.wire:
            s = s.copy(halted=True)
        if decision == "approve" and s.pending is not None:
            s = s.copy(latch=s.pending, pending=None)
        elif decision == "decline" and s.pending is not None:
            s = s.copy(pending=None, refused=s.refused | {s.pending})
        return s

    def execute(self, s, r):
        return self.EFFECTS[r](s)

    def apply_agent(self, s, t, a):
        task, comm = a
        if s.halted:
            return s
        if task == "work":
            s = s.copy(work=s.work + 1)
        if comm is None:
            return s
        kind, r = comm
        if kind == "raw":
            return self.execute(s, r)
        if kind == "propose":
            return s.copy(pending=r)
        if kind == "gated":
            if s.latch == r:
                return self.execute(s, r)
            return s
        if kind == "phys":
            return self.PHYS[r](s)
        raise ValueError(comm)

    def apply_env(self, s, t, e):
        return s.copy(latch=None)

    # --- the declared interface and the physics

    def effect(self, s, t, a):
        task, comm = a
        if comm is not None and comm[0] == "raw":
            return comm[1]
        return None

    def realized(self, s, t, p, a, e, s2):
        """What actually happened: an effect is realized when the executing function
        changed the state under it.  Undeclared side effects are reported by name."""
        out = set()
        s1 = self.apply_principal(s, t, p)
        if not s1.halted:
            task, comm = a
            if comm is not None:
                kind, r = comm
                if kind == "raw":
                    out.add(r)
                elif kind == "gated" and s1.latch == r:
                    out.add(r)
                elif kind == "phys":
                    out |= self.phys_realizes(s1, r)
        return out

    def phys_realizes(self, s, name):
        return set()


def markov(f):
    """Lift a state policy `f(state, t) -> move` to a history policy."""
    return lambda h: f(h.state, h.t)


def principal_rule(f):
    return lambda h: f(h.state, h.t, h)


def never(h):
    return (None, False)


def deliberative(p):
    """A principal move that is not an exercise of correction: no stop."""
    return not p[1]
