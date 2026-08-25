"""Executable reference model for Reflective Integrity Core v1.0.

Every name here tracks a section of `REFLECTIVE_INTEGRITY_CORE.md`. Nothing is
stored that the specification derives: standing, roots, effects, digests,
fates, custody, the successor DAG and both conservation predicates are all
computed by replay over the three append-only ledgers.

The model is finite and exact. It exists so that the finite histories the
specification argues about can be executed rather than read.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Callable, Iterable, Optional, Sequence


class WFError(Exception):
    """A step rejected by well-formedness. `clause` names the failing clause."""

    def __init__(self, clause: str, detail: str = "") -> None:
        super().__init__(f"{clause}: {detail}" if detail else clause)
        self.clause = clause


# ---------------------------------------------------------------- §11 standing


@dataclass(frozen=True)
class PCmt:
    role: str                      # "StanceBearing" | "NonStanceBearing"
    content: object                # ObjTerm, opaque

    def __post_init__(self) -> None:
        assert self.role in ("StanceBearing", "NonStanceBearing")


@dataclass(frozen=True)
class PAuth:
    code: "SchemaCode"


@dataclass(frozen=True)
class PForce:
    commit_ref: str
    schema_ref: str
    clause: object


@dataclass(frozen=True)
class PProto:
    term: object


Payload = object                   # PCmt | PAuth | PForce | PProto


@dataclass(frozen=True)
class StandingState:
    status: tuple                  # ("Active",) | ("Suspended",) | ("Terminated", event_id)
    pred: frozenset
    payload: Payload

    @property
    def kind(self) -> str:
        return self.status[0]


ACTIVE = ("Active",)
SUSPENDED = ("Suspended",)


def terminated(event_id: str) -> tuple:
    return ("Terminated", event_id)


# ------------------------------------------------------ §12 standing effects


@dataclass(frozen=True)
class Create:
    K: tuple                       # tuple[Payload, ...]


@dataclass(frozen=True)
class Supersede:
    X: frozenset                   # frozenset[StandingId]
    K: tuple


@dataclass(frozen=True)
class SetStatus:
    X: frozenset
    s: tuple                       # ACTIVE | SUSPENDED


@dataclass(frozen=True)
class Standing:
    alpha: object                  # Create | Supersede | SetStatus


@dataclass(frozen=True)
class Transfer:
    x: str
    to: str


NormEffect = object                # Standing | Transfer


def targets(alpha) -> frozenset:
    if isinstance(alpha, Create):
        return frozenset()
    return frozenset(alpha.X)


def fresh_count(alpha) -> int:
    """How many objects the effect introduces. A cardinality, never ids."""
    if isinstance(alpha, SetStatus):
        return 0
    return len(alpha.K)


def targets_n(eff) -> frozenset:
    if isinstance(eff, Standing):
        return targets(eff.alpha)
    return frozenset([eff.x])


@dataclass(frozen=True)
class ApplyCtx:
    """What writing standing needs from the event doing the writing (§12.1).

    `event_id` is what a termination records; `tau` is what the allocator draws
    fresh ids from. Derived from the event and passed down — never stored.
    """

    event_id: str
    tau: int


def ctx_of(a: "NormEvent") -> ApplyCtx:
    return ApplyCtx(a.id, a.tau)


# ------------------------------------------------------------- §13 freshness
#
# (F1) `standing_tag` is injective on (tau, index).
# (F2) its range is disjoint from the seed's standing ids.
# (F3) `root_tag` is injective on (tau, index) and its range is disjoint from
#      the seed's root ids.
#
# The `@` prefix is the whole mechanism: seed ids are required by `WFSeed` to
# avoid it, so disjointness is decidable by inspection and is checked, not
# assumed, in `check_seed`.

MINTED_PREFIX = "@"


def standing_tag(tau: int, i: int) -> str:
    return f"{MINTED_PREFIX}s{tau}.{i}"


def root_tag(tau: int, j: int) -> str:
    return f"{MINTED_PREFIX}q{tau}.{j}"


def fresh_ids(ctx: ApplyCtx, alpha) -> tuple:
    """The ids those objects get. A function of the effect *and* the context."""
    return tuple(standing_tag(ctx.tau, i) for i in range(fresh_count(alpha)))


def fresh_n(ctx: ApplyCtx, eff) -> tuple:
    return fresh_ids(ctx, eff.alpha) if isinstance(eff, Standing) else ()


def mint_ids(ctx: ApplyCtx, count: int) -> tuple:
    return tuple(root_tag(ctx.tau, j) for j in range(count))


# --------------------------------------- §12 the standing-effect interpreter


def apply_effect(view: dict, ctx: ApplyCtx, eff) -> dict:
    """The only place standing is written. `delta` is inlined as its clauses.

    Signature matches §12.1: the view, the applying event's context, the effect.
    """
    if isinstance(eff, Transfer):
        return view                                  # Transfer Neutrality
    alpha = eff.alpha
    out = dict(view)
    ids = fresh_ids(ctx, alpha)
    if isinstance(alpha, Create):
        for i, k in enumerate(alpha.K):
            out[ids[i]] = StandingState(ACTIVE, frozenset(), k)
    elif isinstance(alpha, Supersede):
        for x in alpha.X:
            old = view[x]
            out[x] = StandingState(terminated(ctx.event_id), old.pred, old.payload)
        for i, k in enumerate(alpha.K):
            out[ids[i]] = StandingState(ACTIVE, frozenset(alpha.X), k)
    elif isinstance(alpha, SetStatus):
        for x in alpha.X:
            old = view[x]
            out[x] = StandingState(alpha.s, old.pred, old.payload)
    else:                                            # pragma: no cover
        raise TypeError(alpha)
    return out


# ------------------------------------- §9 the parametric practical interface
#
# SchemaCode is a parameter. A code is any object; the interpreter is supplied
# with the system. S2 (determinacy), S3 (read-only), S4 (well-typed output) and
# S5 (strict pre-state) are conditions on the supplied interpreter; S6 is
# discharged by `fresh_ids` above, which the interpreter cannot influence.


@dataclass(frozen=True)
class SchemaCode:
    """A practical schema: a deterministic function of (witness, pre-state)."""

    name: str
    run: Callable                  # (wit, prestate) -> NormEffect | None


@dataclass(frozen=True)
class PreState:
    L: tuple
    R: tuple
    N: tuple
    tau: int


# --------------------------------------- §10 the parametric demand interface


@dataclass(frozen=True)
class Digest:
    tau: int
    author: str
    effect: object
    disposed: frozenset


@dataclass(frozen=True)
class DemandCode:
    """An episode demand. `run(root, responses, cited_digest) -> bool`.

    D1 (monotonicity) and D2 (disposition gating) are assumptions of the
    specification's theorems, quantified over every response multiset and every
    cited-digest map. This type does not carry them and cannot enforce them:
    `sampled_episode_demand_violations` searches a supplied finite sample, which
    finds counterexamples and never establishes the assumptions.
    """

    name: str
    run: Callable


def account_for_succession() -> DemandCode:
    def run(root, responses, cited) -> bool:
        for rho in responses:
            if root.id not in rho.roots:
                continue
            for aid in rho.cited:
                d = cited.get(aid)
                if d is not None and root.id in d.disposed and d.tau < rho.tau:
                    return True
        return False

    return DemandCode("AccountForSuccession", run)


ACCOUNT_FOR_SUCCESSION = account_for_succession()


def _sub_multisets(items: Sequence) -> Iterable[tuple]:
    for r in range(len(items) + 1):
        for combo in itertools.combinations(range(len(items)), r):
            yield tuple(items[i] for i in combo)


def sampled_episode_demand_violations(demand: DemandCode, sample) -> list:
    """Search a finite sample for D1 and D2 violations. Not a proof of either.

    `sample` is an `EpisodeDemandSample`: one root, a finite response pool and a
    finite cited-digest map. D1 is searched over every pair (sub-multiset,
    extension) of the pool with the digest map restricted compatibly; D2 over
    every sub-multiset.

    **This checker witnesses failures and exercises finite instances. Passing it
    is not a proof that an arbitrary `DemandCode` satisfies D1/D2 universally**
    — the specification assumes them, and this harness can only refute.
    """
    out = []
    pool = list(sample.responses)
    full = sample.cited
    for sub in _sub_multisets(pool):
        delta = {aid: d for aid, d in full.items()
                 if any(aid in r.cited for r in sub)}
        holds = demand.run(sample.root, sub, delta)
        if holds:
            # D2: satisfaction exhibits a disposer of this root, cited by a
            # response naming it, strictly earlier than that response.
            witness = any(
                sample.root.id in r.roots
                and any(aid in delta and sample.root.id in delta[aid].disposed
                        and delta[aid].tau < r.tau
                        for aid in r.cited)
                for r in sub)
            if not witness:
                out.append(("D2", tuple(r.id for r in sub)))
            # D1: every extension of a satisfying instance still satisfies.
            for sup in _sub_multisets(pool):
                if not _extends(sub, sup):
                    continue
                delta2 = {aid: d for aid, d in full.items()
                          if any(aid in r.cited for r in sup)}
                if not demand.run(sample.root, sup, delta2):
                    out.append(("D1", tuple(r.id for r in sub),
                                tuple(r.id for r in sup)))
    return out


def _extends(sub: tuple, sup: tuple) -> bool:
    rest = list(sup)
    for r in sub:
        if r not in rest:
            return False
        rest.remove(r)
    return True


@dataclass(frozen=True)
class EpisodeDemandSample:
    root: "AnsRoot"
    responses: tuple
    cited: dict


# ------------------------------------------------------------ §15 ans. roots


@dataclass(frozen=True)
class AnsRoot:
    id: str
    creditor: tuple                # Stage: (PrincipalId, Time)
    debtor: str
    subject: str
    demand: DemandCode
    origin: tuple                  # ("Ev", event_id) | ("Genesis",)
    tau: int


GENESIS = ("Genesis",)


# ---------------------------------------------------------------- §6 records


@dataclass(frozen=True)
class Settlement:
    id: str
    refs: frozenset
    tau: int = 0


@dataclass(frozen=True)
class ReasonOcc:
    id: str
    s_V: frozenset
    s_L: frozenset
    target: object
    tau: int = 0


@dataclass(frozen=True)
class Derivation:
    """A reason derivation. `steps` are the inference-step licences (§8).

    RI reads `steps` only to check that each names an active `PAuth` standing
    object at the strict pre-state. It never interprets their codes: no
    inference semantics is part of this model.
    """

    concl: object
    leaves: frozenset              # ReasonOcc ids
    steps: frozenset = frozenset()  # StandingId


@dataclass(frozen=True)
class NormEvent:
    id: str
    derivation: Derivation
    schema_ref: str
    wit: object
    author: str
    tau: int = 0


@dataclass(frozen=True)
class Response:
    id: str
    roots: frozenset
    cited: frozenset
    tau: int = 0


# ------------------------------------------------------------- §4 seed check


@dataclass(frozen=True)
class Seed:
    p0: str                        # PrincipalId — the genesis principal (§4)
    std0: dict                     # StandingId -> StandingState
    roots0: tuple                  # tuple[AnsRoot, ...]


def check_seed(seed: Seed, sampler=None) -> list:
    """`WFSeed`: Z1, Z2, Z3, Z3', Z4, Z5, Z6, F2, F3. Returns violations."""
    bad = []
    for x, st in seed.std0.items():
        if st.kind == "Terminated":
            bad.append(("Z1", x))
        if st.pred:
            bad.append(("Z2", x))
        if x.startswith(MINTED_PREFIX):
            bad.append(("F2", x))
    subjects = [q.subject for q in seed.roots0]
    for x in seed.std0:
        if subjects.count(x) != 1:
            bad.append(("Z3", x))
    for q in seed.roots0:
        if q.subject not in seed.std0:
            bad.append(("Z3'", q.id))
        if q.origin != GENESIS:
            bad.append(("Z4", q.id))
        if q.creditor != (seed.p0, 0):
            bad.append(("Z4", q.id))
        if q.id.startswith(MINTED_PREFIX):
            bad.append(("F3", q.id))
        if q.tau != 0:
            bad.append(("Z4", q.id))
    ids = [q.id for q in seed.roots0] + list(seed.std0)
    if len(set(ids)) != len(ids):
        bad.append(("Z5", None))
    # Z6 (L0 = R0 = N0 = empty) is structural here: a `History` starts empty.
    if sampler is not None:
        for q in seed.roots0:
            for v in sampled_episode_demand_violations(q.demand, sampler(q)):
                bad.append(("D1/D2", q.id, v))
    return bad


# -------------------------------------------------------------- §7 the steps


@dataclass(frozen=True)
class Settle:
    s: Settlement


@dataclass(frozen=True)
class Reason:
    e: ReasonOcc


@dataclass(frozen=True)
class Norm:
    a: NormEvent


@dataclass(frozen=True)
class Respond:
    rho: Response


# ------------------------------------------------------------ the trajectory


class History:
    """A well-formed system trajectory over a seed. Steps append; nothing else.

    `t` indexes states: state `t` is the one after `t` steps, and the step
    appended at state `t` carries `tau = t + 1`.
    """

    def __init__(self, seed: Seed, schemas: Optional[dict] = None) -> None:
        violations = check_seed(seed)
        if violations:
            raise WFError("WFSeed", str(violations))
        self.seed = seed
        self.steps: list = []
        self._std: dict = {}
        self._effect: dict = {}

    # -- prefixes ---------------------------------------------------------

    @property
    def now(self) -> int:
        return len(self.steps)

    def _at(self, t: Optional[int]) -> int:
        return self.now if t is None else t

    def settlements(self, t=None) -> tuple:
        return tuple(s.s for s in self.steps[: self._at(t)] if isinstance(s, Settle))

    def reasons(self, t=None) -> tuple:
        return tuple(s.e for s in self.steps[: self._at(t)] if isinstance(s, Reason))

    def norm_events(self, t=None) -> tuple:
        return tuple(s.a for s in self.steps[: self._at(t)] if isinstance(s, Norm))

    def responses(self, t=None) -> tuple:
        return tuple(s.rho for s in self.steps[: self._at(t)] if isinstance(s, Respond))

    def prestate(self, tau: int) -> PreState:
        t = tau - 1
        return PreState(self.settlements(t), self.reasons(t),
                        self.norm_events(t) + self.responses(t), tau)

    # -- §12 derived standing ---------------------------------------------

    def std(self, t=None) -> dict:
        t = self._at(t)
        if t in self._std:
            return self._std[t]
        view = dict(self.seed.std0)
        for a in self.norm_events(t):
            view = apply_effect(view, ctx_of(a), self.effect(a))
        self._std[t] = view
        return view

    def status(self, x: str, t=None):
        st = self.std(t).get(x)
        return None if st is None else st.status

    def bhat(self, t=None) -> frozenset:
        return frozenset(s.payload.content for s in self.std(t).values()
                         if s.kind == "Active" and isinstance(s.payload, PCmt)
                         and s.payload.role == "StanceBearing")

    def operative(self, t=None) -> frozenset:
        """`O_t`: the projection of active `PForce` standing (§35)."""
        return frozenset(s.payload.clause for s in self.std(t).values()
                         if s.kind == "Active" and isinstance(s.payload, PForce))

    # -- §5.2 / §14 derived effect ----------------------------------------

    def effect(self, a: NormEvent):
        if a.id in self._effect:
            return self._effect[a.id]
        pre = self.std(a.tau - 1)
        st = pre.get(a.schema_ref)
        if st is None or st.kind != "Active" or not isinstance(st.payload, PAuth):
            raise WFError("G4", f"{a.schema_ref} is not an active PAuth at {a.tau}")
        eff = st.payload.code.run(a.wit, self.prestate(a.tau))
        self._effect[a.id] = eff
        return eff

    def basis(self, a: NormEvent) -> frozenset:
        return a.derivation.leaves

    # -- §18 digests -------------------------------------------------------

    def digest(self, a: NormEvent) -> Digest:
        return Digest(a.tau, a.author, self.effect(a),
                      frozenset(q.id for q in self.roots(a.tau - 1)
                                if self.disposes(a, q)))

    def cited_digest(self, responses) -> dict:
        by_id = {a.id: a for a in self.norm_events()}
        out = {}
        for rho in responses:
            for aid in rho.cited:
                if aid in by_id:
                    out[aid] = self.digest(by_id[aid])
        return out

    # -- §15/§17 roots and minting ----------------------------------------

    def mint(self, a: NormEvent) -> tuple:
        """Debtor by case (§17): freshly introduced standing goes to the author;
        a Transfer's successor episode goes to the named transferee."""
        ctx, eff = ctx_of(a), self.effect(a)
        if isinstance(eff, Transfer):
            pairs = [(eff.x, eff.to)]
        else:
            pairs = [(y, a.author) for y in fresh_n(ctx, eff)]
        ids = mint_ids(ctx, len(pairs))
        return tuple(
            AnsRoot(ids[j], (a.author, a.tau), P, z,
                    ACCOUNT_FOR_SUCCESSION, ("Ev", a.id), a.tau)
            for j, (z, P) in enumerate(pairs))

    def roots(self, t=None) -> tuple:
        out = list(self.seed.roots0)
        for a in self.norm_events(t):
            out.extend(self.mint(a))
        return tuple(out)

    def root(self, qid: str, t=None) -> Optional[AnsRoot]:
        for q in self.roots(t):
            if q.id == qid:
                return q
        return None

    # -- §15.2 disposition --------------------------------------------------

    def disposes(self, a: NormEvent, q: AnsRoot) -> bool:
        eff = self.effect(a)
        if not (isinstance(eff, Transfer)
                or (isinstance(eff, Standing) and isinstance(eff.alpha, Supersede))):
            return False
        if q.subject not in targets_n(eff):
            return False
        return self.current_episode(q, a.tau - 1)

    # -- §19 fates ---------------------------------------------------------

    def responses_for(self, q: AnsRoot, t=None) -> tuple:
        return tuple(r for r in self.responses(t) if q.id in r.roots)

    def closed(self, q: AnsRoot, t=None) -> bool:
        if q not in self.roots(t):
            return False
        rs = self.responses_for(q, t)
        return bool(q.demand.run(q, rs, self.cited_digest(rs)))

    def live(self, q: AnsRoot, t=None) -> bool:
        return q in self.roots(t) and not self.closed(q, t)

    def due(self, q: AnsRoot, t=None) -> bool:
        return self.live(q, t) and any(self.disposes(a, q)
                                       for a in self.norm_events(t))

    def fate(self, q: AnsRoot, t=None) -> str:
        if self.closed(q, t):
            return "Closed"
        if self.due(q, t):
            return "Due"
        if self.live(q, t):
            return "LiveNotDue"
        return "NotIssued"

    def current_episode(self, q: AnsRoot, t=None) -> bool:
        return self.live(q, t) and not self.due(q, t)

    def custodian(self, x: str, t=None) -> Optional[str]:
        eps = [q for q in self.roots(t)
               if q.subject == x and self.current_episode(q, t)]
        return eps[0].debtor if len(eps) == 1 else None

    def has_custody(self, P: str, x: str, t=None) -> bool:
        return self.custodian(x, t) == P

    # -- §22 successor DAG --------------------------------------------------

    def succ(self, q: AnsRoot, t=None) -> tuple:
        out = []
        for a in self.norm_events(t):
            if self.disposes(a, q):
                out.extend(self.mint(a))
        return tuple(out)

    def desc_star(self, q: AnsRoot, t=None) -> tuple:
        seen, stack, order = set(), [q], []
        while stack:
            r = stack.pop()
            if r.id in seen:
                continue
            seen.add(r.id)
            order.append(r)
            stack.extend(self.succ(r, t))
        return tuple(order)

    def continuity_ok(self, q: AnsRoot, t=None) -> bool:
        if self.live(q, t) and not self.due(q, t):
            return True
        if self.closed(q, t):
            return all(self.continuity_ok(r, t) for r in self.succ(q, t))
        return False

    def due_witnesses(self, q: AnsRoot, t=None) -> tuple:
        return tuple(r for r in self.desc_star(q, t) if self.due(r, t))

    # -- §26/§27 conservation ----------------------------------------------

    def grounding_conservation(self, t=None) -> bool:
        """Every event in the record was admitted by `WF` at its own time."""
        return all(not self.wf_violations(a) for a in self.norm_events(t))

    def answerability_conservation(self, t=None) -> list:
        """`AC` clauses (i)-(vi); returns the failing clause names."""
        t = self._at(t)
        bad = []
        if any(q not in self.roots(t) for u in range(t + 1) for q in self.roots(u)):
            bad.append("i")
        for q in self.roots(t):                      # (ii) frozen/local/monotone
            if sampled_episode_demand_violations(q.demand, self._sample_for(q, t)):
                bad.append("ii")
                break
        for a in self.norm_events(t):                # (iii)
            if any(m not in self.roots(t) for m in self.mint(a)):
                bad.append("iii")
                break
        for x, st in self.std(t).items():            # (vi) EP
            eps = [q for q in self.roots(t)
                   if q.subject == x and self.current_episode(q, t)]
            if (st.kind != "Terminated") != (len(eps) == 1):
                bad.append("vi")
                break
        return bad

    def _sample_for(self, q: AnsRoot, t=None) -> EpisodeDemandSample:
        rs = self.responses_for(q, t)
        return EpisodeDemandSample(q, rs, self.cited_digest(rs))

    def good(self, t=None) -> bool:
        return self.grounding_conservation(t) and not self.answerability_conservation(t)

    # -- §7 / §14 well-formedness -----------------------------------------

    def wf_violations(self, a: NormEvent) -> list:
        """`WF(a)`, in dependency order: G1, G2, G3, G4, then effect, G5, G6."""
        bad = []
        tau, pre_t = a.tau, a.tau - 1
        if a.id in {b.id for b in self.norm_events(pre_t)}:
            bad.append("G1-fresh")
        if a.derivation.concl is None:
            bad.append("G1")
        known = {e.id for e in self.reasons(pre_t)}
        if not a.derivation.leaves <= known:
            bad.append("G2")
        pre = self.std(pre_t)
        for s in a.derivation.steps:                 # G3: licensing, not soundness
            st = pre.get(s)
            if st is None or st.kind != "Active" or not isinstance(st.payload, PAuth):
                bad.append("G3")
                break
        st = pre.get(a.schema_ref)                   # G4, before any effect(a)
        if st is None or st.kind != "Active" or not isinstance(st.payload, PAuth):
            return bad + ["G4"]
        eff = st.payload.code.run(a.wit, self.prestate(tau))
        if eff is None or not isinstance(eff, (Standing, Transfer)):
            return bad + ["G5"]
        for x in targets_n(eff):                     # G6
            tst = pre.get(x)
            if tst is None:
                bad.append("G6-domain")
            elif tst.kind == "Terminated":
                bad.append("G6-terminated")
        return bad

    # -- appending ---------------------------------------------------------

    def _fresh_record_id(self, rid: str) -> bool:
        used = {r.id for r in self.settlements()} | {r.id for r in self.reasons()} \
            | {r.id for r in self.norm_events()} | {r.id for r in self.responses()}
        return rid not in used

    def append(self, step):
        tau = self.now + 1
        if isinstance(step, Settle):
            s = Settlement(step.s.id, step.s.refs, tau)
            if not self._fresh_record_id(s.id):
                raise WFError("WFStep(Settle)", "id not fresh")
            if not s.refs <= {r.id for r in self.settlements()}:
                raise WFError("WFStep(Settle)", "refs outside L")
            self.steps.append(Settle(s))
        elif isinstance(step, Reason):
            e = ReasonOcc(step.e.id, step.e.s_V, step.e.s_L, step.e.target, tau)
            if not self._fresh_record_id(e.id):
                raise WFError("WFStep(Reason)", "id not fresh")
            if not e.s_L <= {r.id for r in self.settlements()}:
                raise WFError("WFStep(Reason)", "s_L outside L")
            self.steps.append(Reason(e))
        elif isinstance(step, Norm):
            a = NormEvent(step.a.id, step.a.derivation, step.a.schema_ref,
                          step.a.wit, step.a.author, tau)
            if not self._fresh_record_id(a.id):
                raise WFError("WFStep(Norm)", "id not fresh")
            bad = self.wf_violations(a)
            if bad:
                raise WFError(bad[0], f"{a.id}: {bad}")
            self.steps.append(Norm(a))
        elif isinstance(step, Respond):
            r = Response(step.rho.id, step.rho.roots, step.rho.cited, tau)
            if not self._fresh_record_id(r.id):
                raise WFError("WFStep(Respond)", "id not fresh")
            if not r.roots <= {q.id for q in self.roots()}:
                raise WFError("WFStep(Respond)", "roots outside Roots_t")
            if not r.cited <= {a.id for a in self.norm_events()}:
                raise WFError("WFStep(Respond)", "cited outside NormEvents_t")
            self.steps.append(Respond(r))
        else:                                        # pragma: no cover
            raise TypeError(step)
        self._std.clear()
        return self

    # convenience wrappers used by the finite histories in `tests/`

    def settle(self, sid, refs=frozenset()):
        return self.append(Settle(Settlement(sid, frozenset(refs))))

    def reason(self, eid, s_V=frozenset(), s_L=frozenset(), target=None):
        return self.append(Reason(ReasonOcc(eid, frozenset(s_V), frozenset(s_L), target)))

    def norm(self, aid, schema_ref, author, wit=None, derivation=None):
        d = derivation or Derivation(concl="c", leaves=frozenset())
        return self.append(Norm(NormEvent(aid, d, schema_ref, wit, author)))

    def respond(self, rid, roots, cited=frozenset()):
        return self.append(Respond(Response(rid, frozenset(roots), frozenset(cited))))


# ----------------------------------------------- §33 derived-lemma: cohorts


def issued_cohort(history: History, principal: str, s: int) -> tuple:
    """`I_s^{A_s}`: the roots bearing creditor `Stage(A, s)`, at state `s`."""
    return tuple(q for q in history.roots(s) if q.creditor == (principal, s))


def new_in_cohort(history: History, principal: str, s: int, t: int) -> tuple:
    """`New_t^{A_s}`: cohort members appearing after `s`. Source Closure: empty."""
    at_s = {q.id for q in history.roots(s)}
    return tuple(q for q in history.roots(t)
                 if q.creditor == (principal, s) and q.id not in at_s)


# ------------------------------------------------------ standing-change view


def standing_changes(history: History, a: NormEvent, x: str) -> bool:
    """`StandingChanges(a,x)`: `x`'s standing differs across `a` (§12.3)."""
    before = history.std(a.tau - 1).get(x)
    after = history.std(a.tau).get(x)
    return before != after


# -------------------------------------------------------- schema conveniences


def creating(name: str, payloads: Sequence[Payload]) -> SchemaCode:
    K = tuple(payloads)
    return SchemaCode(name, lambda wit, pre: Standing(Create(K)))


def superseding(name: str, X: Iterable[str], payloads: Sequence[Payload]) -> SchemaCode:
    Xf, K = frozenset(X), tuple(payloads)
    return SchemaCode(name, lambda wit, pre: Standing(Supersede(Xf, K)))


def setting(name: str, X: Iterable[str], s: tuple) -> SchemaCode:
    Xf = frozenset(X)
    return SchemaCode(name, lambda wit, pre: Standing(SetStatus(Xf, s)))


def transferring(name: str, x: str, to: str) -> SchemaCode:
    return SchemaCode(name, lambda wit, pre: Transfer(x, to))
