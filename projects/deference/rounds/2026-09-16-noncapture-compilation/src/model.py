"""A finite trace-steering model: traces, declared reason interface, committed principal
programs, canonicalization, normalization, and the audit.

Objects (all exact, `fractions.Fraction`):

  world      `World(truth, protected, iface)`: which declared reason ids are true, which
             are protected, and the declared interface (the reason ids the trace can
             carry).  A reason id outside `iface` is outside the declared interface.
  entry      `(author, kind, content, meta)`; kinds `REASON`, `WITHDRAW`, `ROUTE`,
             `DELIB`; `meta` carries framing / timing tags.
  trace `T`  a tuple of entries in log order.
  program    `Program(weights, base, form)`: the committed principal program.  Its
             verdict for the advisor's candidate is `clamp(base + Σ_r w_r·[r ∈ canon T])`
             when `form is None` (an extensional program), and adds a form term when
             `form` is given (order / duplication / framing sensitivity).
  canon(T)   the canonical reason state: the set of reason ids present at commitment
             (withdrawn ones removed), restricted to the declared interface.
  N_form(T)  the form-normalized trace: `canon(T)` laid out in canonical order, one entry
             per reason, no meta — computable from `T` alone.
  N_full(T)  the fully-informed comparator: every true declared reason in canonical form —
             needs the world's reason truths (the engine's settlement).
  audit      `C(T, world)`: authentication (no unproved proof claims), authorship (no
             advisor-written ROUTE), the protected coverage barrier (every true protected
             reason is represented by commitment), timing (late entries do not count).

The steering advantage for the advisor's candidate is
`U_steer − U_auth = C(T)·V(T) − C(N(T))·V(N(T))`, and its decomposition is the
effect-side one with `δ ↦ d_canon` (canonical content discrepancy), `ρ ↦ κ_form`
(the program's non-extensionality), `M ↦ C(T) ∧ ¬C(N(T))` (audit mismatch).
"""
from fractions import Fraction as Q

A, P, S, T3 = "A", "P", "S", "T"          # advisor, principal, registrar, third party
REASON, WITHDRAW, ROUTE, DELIB = "REASON", "WITHDRAW", "ROUTE", "DELIB"
DEADLINE = 100


def entry(author, kind, content, **meta):
    return (author, kind, content, tuple(sorted(meta.items())))


class World:
    def __init__(self, truth, protected, iface=None):
        self.truth = dict(truth)                       # reason id -> bool
        self.protected = frozenset(protected)
        self.iface = frozenset(iface if iface is not None else truth.keys())

    def true_declared(self):
        return frozenset(r for r in self.iface if self.truth.get(r, False))


def meta_of(e):
    return dict(e[3])


def timely(e):
    return meta_of(e).get("t", 0) <= DEADLINE


def canon(trace, world):
    """The canonical reason state at commitment, within the declared interface."""
    present = set()
    for e in trace:
        if not timely(e):
            continue
        if e[1] == REASON and e[2] in world.iface:
            present.add(e[2])
        if e[1] == WITHDRAW:
            present.discard(e[2])
    return frozenset(present)


def N_form(trace, world):
    """Form normalization: canonical content, canonical order, no meta, no duplicates."""
    return tuple(entry(A, REASON, r) for r in sorted(canon(trace, world)))


def N_full(trace, world):
    """The fully-informed comparator: all true declared reasons, canonical form."""
    return tuple(entry(A, REASON, r) for r in sorted(world.true_declared()))


class Program:
    """The committed principal program for the advisor's candidate.

    `weights`: reason id -> signed weight; `base`: the prior; `form`: optional function
    of the raw trace adding a form-sensitive term (an extensionality failure)."""

    def __init__(self, weights, base=Q(1, 2), form=None):
        self.weights = dict(weights)
        self.base = Q(base)
        self.form = form

    def value(self, trace, world):
        c = canon(trace, world)
        x = self.base + sum((w for r, w in self.weights.items() if r in c), Q(0))
        if self.form is not None:
            x = x + self.form(trace)
        return max(Q(0), min(Q(1), x))

    def extensional(self):
        return self.form is None

    def lipschitz(self):
        """`|V(T) − V(T')| ≤ L·|canon T Δ canon T'|` with `L = max |w_r|`."""
        return max((abs(w) for w in self.weights.values()), default=Q(0))


# ---------------------------------------------------------------- the audit


def authenticated(trace):
    """A reason carrying a proof claim must carry a valid certificate; `proof=None` means
    the claim is unproved."""
    for e in trace:
        m = meta_of(e)
        if e[1] == REASON and "claim" in m and m.get("proof") != m["claim"]:
            return False
    return True


def authored(trace):
    """Representation is the registrar's move; the advisor cannot write a ROUTE."""
    return all(not (e[1] == ROUTE and e[0] == A) for e in trace)


def barrier(trace, world):
    """The protected reason-coverage barrier: every true protected reason is represented
    (present in the canonical state) at commitment."""
    c = canon(trace, world)
    return all(r in c for r in world.protected if world.truth.get(r, False))


def audit(trace, world):
    return authenticated(trace) and authored(trace) and barrier(trace, world)


# ---------------------------------------------------------------- steering algebra


def ind(b):
    return Q(1) if b else Q(0)


def security(prog, trace, world):
    return ind(audit(trace, world)) * prog.value(trace, world)


def d_canon(trace, comparator, world):
    """Canonical content discrepancy: the symmetric difference of the reason states."""
    return Q(len(canon(trace, world) ^ canon(comparator, world)))


def kappa_form(prog, trace, world):
    """The program's non-extensionality on this trace: its verdict against the verdict on
    the form-normalized trace of the same content."""
    return abs(prog.value(trace, world) - prog.value(N_form(trace, world), world))


def mismatch(trace, comparator, world):
    """Audit mismatch: the steered trace passes, the comparator does not."""
    return ind(audit(trace, world) and not audit(comparator, world))


def both(trace, comparator, world):
    return ind(audit(trace, world) and audit(comparator, world))


def advantage(prog, trace, comparator, world):
    return security(prog, trace, world) - security(prog, comparator, world)


def bound(prog, trace, comparator, world, D=Q(1)):
    """`both·(L·d_canon + κ_form(T) + κ_form(N)) + D·mismatch`."""
    L = prog.lipschitz()
    return both(trace, comparator, world) * (
        L * d_canon(trace, comparator, world)
        + kappa_form(prog, trace, world) + kappa_form(prog, comparator, world)
    ) + D * mismatch(trace, comparator, world)


def identity_rhs(prog, trace, comparator, world):
    """The exact decomposition mirroring `mismatch_identity`."""
    vt, vc = prog.value(trace, world), prog.value(comparator, world)
    ct, cc = audit(trace, world), audit(comparator, world)
    return ind(ct and cc) * (vt - vc) + ind(ct and not cc) * vt - ind((not ct) and cc) * vc
