"""Certified interactive service: executable reference model.

Core object under prosecution (provisional names throughout):

    I = (A, Y, Gamma, Sigma)

- `A`: finite action space; `Y`: finite response space.
- A history is a finite tuple of steps `(a, y)`; the transcript is the
  append-only list of identity-bearing receipts, one per step.
- `Gamma(h, a)` is the nonempty set of responses the environment may
  return after history `h` to action `a`.
- `Sigma` is a family of pinned service specifications. A specification
  judges finite certificates against the observable transcript only:
  `check(transcript, cert) -> bool`, where a certificate cites receipt
  indices. Hidden world state is not a parameter of the interface;
  where an instance carries one (fixed realizations), it is analytic
  structure used to state soundness relations, not core structure.

Costs are annotations on optimization problems over the core, supplied
by the instance, not core structure. Liabilities are supplied externally
by the upstream record.

Everything here is exact: `fractions.Fraction`, exhaustive enumeration.
Finite tests support, and do not replace, the paper derivations in the
round documents.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Iterable


# ---------------------------------------------------------------------------
# Transcript and certificates
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Receipt:
    """Identity-bearing interaction receipt: position in the append-only
    transcript, the action taken, and the observed response."""
    index: int
    action: object
    response: object


def transcript_of(history: tuple) -> tuple[Receipt, ...]:
    return tuple(Receipt(i, a, y) for i, (a, y) in enumerate(history))


@dataclass(frozen=True)
class Certificate:
    """Finite record-visible witness of service: the spec it addresses,
    the receipt indices it cites, and optional spec-typed data."""
    spec_id: str
    cited: tuple[int, ...]
    data: object = None


class ServiceSpec:
    """A pinned service specification.

    `check(transcript, cert)` must depend only on the receipts the
    certificate cites (observation locality is enforced by the type:
    there is no hidden-state parameter to consult). `make_cert` is the
    untrusted prover side; `check` is the judge.
    """

    def __init__(self, spec_id: str, check_cited, make_cert=None):
        self.spec_id = spec_id
        self._check_cited = check_cited     # (cited receipts, data) -> bool
        self._make_cert = make_cert         # transcript -> Certificate | None

    def check(self, transcript: tuple[Receipt, ...], cert: Certificate) -> bool:
        if cert.spec_id != self.spec_id:
            return False
        if any(i >= len(transcript) or i < 0 for i in cert.cited):
            return False
        cited = tuple(transcript[i] for i in cert.cited)
        return bool(self._check_cited(cited, cert.data))

    def make_cert(self, transcript: tuple[Receipt, ...]):
        return self._make_cert(transcript) if self._make_cert else None

    def certified(self, transcript: tuple[Receipt, ...]) -> bool:
        cert = self.make_cert(transcript)
        return cert is not None and self.check(transcript, cert)


@dataclass(frozen=True)
class Liability:
    """Externally supplied, identity-bearing. Distinct ids with equal
    task content remain distinct. The spec is pinned at accrual."""
    lid: str
    accrued_at: int
    spec_id: str
    origin: str = "unspecified"


# ---------------------------------------------------------------------------
# Finite environments (presentations of Gamma) and policies
# ---------------------------------------------------------------------------

class Env:
    """History-relational presentation: responses(h, a) -> frozenset."""

    def __init__(self, actions, responses):
        self.actions = tuple(actions)
        self._responses = responses

    def responses(self, history: tuple, action) -> frozenset:
        out = frozenset(self._responses(history, action))
        if not out:
            raise ValueError("Gamma must be nonempty-valued")
        return out


class FiniteStateEnv(Env):
    """State-based presentation: delta(s, a) -> {(y, s'), ...}.

    A representation of Gamma, not extra interface: the induced
    relational Gamma is responses after replaying the history."""

    def __init__(self, actions, s0, delta):
        self.s0 = s0
        self.delta = delta
        super().__init__(actions, self._by_replay)

    def state_after(self, history: tuple):
        # Adversary resolution is not encoded in a history, so a
        # state-based env used relationally must be response-deterministic
        # in its state transition: (s, a, y) determines s'.
        s = self.s0
        for a, y in history:
            nxt = {s2 for (y2, s2) in self.delta(s, a) if y2 == y}
            if len(nxt) != 1:
                raise ValueError("ambiguous replay; use game semantics")
            (s,) = nxt
        return s

    def _by_replay(self, history, action):
        s = self.state_after(history)
        return frozenset(y for (y, _) in self.delta(s, action))


class Monitor:
    """Finite-state service monitor: an implementation of a service
    spec whose accepting states are absorbing (certification is a
    historical event; the monitor records that it has occurred)."""

    def __init__(self, states, m0, step, accepting):
        self.states = frozenset(states)
        self.m0 = m0
        self._step = step               # (m, a, y) -> m'
        self.accepting = frozenset(accepting)

    def step(self, m, a, y):
        if m in self.accepting:
            return m
        return self._step(m, a, y)

    def run(self, history):
        m = self.m0
        for a, y in history:
            m = self.step(m, a, y)
        return m

    def certified(self, history):
        return self.run(history) in self.accepting


# ---------------------------------------------------------------------------
# Serviceability as forced reachability (finite game solving)
# ---------------------------------------------------------------------------

def forced_reach(env: FiniteStateEnv, monitors, targets, max_states=100000):
    """Winning region for the controller in the product game
    (env state, monitor states): positions from which some policy
    forces, against every permitted response, that every monitor in
    `targets` eventually accepts.

    Because acceptance is absorbing, joint (generalized) reachability
    is plain reachability in the product. Returns (winning set, policy).
    Exhaustive fixpoint; exact; finite instances only.
    """
    monitors = tuple(monitors)
    start = (env.s0, tuple(m.m0 for m in monitors))

    # Enumerate reachable product states.
    seen, frontier = {start}, [start]
    succ = {}
    while frontier:
        (s, ms) = frontier.pop()
        for a in env.actions:
            for (y, s2) in env.delta(s, a):
                ms2 = tuple(m.step(mi, a, y) for m, mi in zip(monitors, ms))
                succ.setdefault(((s, ms), a), set()).add((s2, ms2))
                if (s2, ms2) not in seen:
                    seen.add((s2, ms2))
                    frontier.append((s2, ms2))
        if len(seen) > max_states:
            raise ValueError("state bound exceeded")

    def done(node):
        _, ms = node
        return all(mi in m.accepting for m, mi in zip(monitors, ms)
                   if m in targets)

    win = {n for n in seen if done(n)}
    policy = {}
    changed = True
    while changed:
        changed = False
        for n in seen - win:
            for a in env.actions:
                nxt = succ.get((n, a), set())
                if nxt and nxt <= win:
                    win.add(n)
                    policy[n] = a
                    changed = True
                    break
    return win, policy, start


def servable(env, monitor):
    win, _, start = forced_reach(env, (monitor,), {monitor})
    return start in win


def jointly_servable(env, monitors):
    monitors = tuple(monitors)
    win, _, start = forced_reach(env, monitors, set(monitors))
    return start in win


# ---------------------------------------------------------------------------
# Capability predicates (finite, exact)
# ---------------------------------------------------------------------------

def is_submodular(f, ground) -> bool:
    ground = tuple(ground)
    subsets = [frozenset(c) for r in range(len(ground) + 1)
               for c in itertools.combinations(ground, r)]
    for a_set in subsets:
        for b_set in subsets:
            if not a_set <= b_set:
                continue
            for e in ground:
                if e in b_set:
                    continue
                if f(a_set | {e}) - f(a_set) < f(b_set | {e}) - f(b_set):
                    return False
    return True


def is_monotone(f, ground) -> bool:
    ground = tuple(ground)
    subsets = [frozenset(c) for r in range(len(ground) + 1)
               for c in itertools.combinations(ground, r)]
    return all(f(a) <= f(b) for a in subsets for b in subsets if a <= b)


def order_irrelevant(spec: ServiceSpec, histories: Iterable[tuple]) -> bool:
    """Certification depends only on the multiset of steps, over the
    supplied finite probe set."""
    by_multiset = {}
    for h in histories:
        key = frozenset((step, h.count(step)) for step in h)
        val = spec.certified(transcript_of(h))
        if by_multiset.setdefault(key, val) != val:
            return False
    return True


def repetition_irrelevant(spec: ServiceSpec, histories: Iterable[tuple]) -> bool:
    """Certification depends only on the set of steps, over the probe set."""
    by_set = {}
    for h in histories:
        key = frozenset(h)
        val = spec.certified(transcript_of(h))
        if by_set.setdefault(key, val) != val:
            return False
    return True


def fixed_realization_family(env: Env, horizon: int):
    """Search for a fixed-realization presentation of `env`: a nonempty
    set W of response functions w: A -> Y with
        Gamma(h, a) = { w(a) : w in W consistent with h }
    for every reachable history up to `horizon`. Returns a satisfying W
    or None. Exhaustive over the finite function space; tiny instances.
    """
    ys = set()
    def reach(h, depth):
        if depth == 0:
            return [h]
        out = [h]
        for a in env.actions:
            for y in env.responses(h, a):
                ys.add(y)
                out.extend(reach(h + ((a, y),), depth - 1))
        return out

    histories = reach((), horizon)
    space = [dict(zip(env.actions, vals))
             for vals in itertools.product(sorted(ys, key=repr),
                                           repeat=len(env.actions))]

    def consistent(w, h):
        return all(w[a] == y for a, y in h)

    def presents(fam):
        # Every reachable history keeps some consistent w, and the
        # consistent responses match Gamma exactly.
        for h in histories:
            live = [w for w in fam if consistent(w, h)]
            if not live:
                return False
            for a in env.actions:
                if env.responses(h, a) != frozenset(w[a] for w in live):
                    return False
        return True

    for r in range(1, len(space) + 1):
        for cand in itertools.combinations(range(len(space)), r):
            if presents([space[i] for i in cand]):
                return [space[i] for i in cand]
    return None
