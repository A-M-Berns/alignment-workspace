"""Exact translations of the five prior models into the generic
certified-interactive-service interface, with both sides' objectives
computed independently so finite tests can compare them term by term.

Sources (primary PDFs inspected; see PROVENANCE.md):
- Set Cover with Delay (SCD): Azar, Chiplunkar, Kutten, Touitou,
  ESA 2020, arXiv 1807.08543v3, Section 2.
- Minimum Latency Submodular Cover (MLSC) / Submodular Ranking:
  Im, Nagarajan, van der Zwaan, ACM TALG 13(1), arXiv 1110.2207v3,
  Sections 1-1.1.
- Adaptive Submodularity: Golovin, Krause, JAIR 42 (2011),
  arXiv 1003.3967v5, Sections 2-3, 5.2 (Definitions 1-3, 7, 8).
- Interactive Submodular Set Cover (ISSC): Guillory, Bilmes,
  ICML 2010, arXiv 1002.3345v2, Sections 2-3.
- Request-Response games: Horn, Thomas, Wallmeier, Zimmermann,
  arXiv 1406.4648v1, Sections 2-3.

Discrete conventions are declared where the source is continuous.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction

from service_core import Certificate, Env, ServiceSpec, transcript_of


# ---------------------------------------------------------------------------
# A. Set Cover with Delay (discrete-event restriction)
# ---------------------------------------------------------------------------
# Paper model: requests q_j arrive on elements at time r_j with momentary
# delay d_j(t); buying set S_i at time t costs c(S_i) >= 1 and serves all
# then-pending requests on its elements (never future arrivals); requests
# may go permanently unserved (footnote 2). Discrete restriction here:
# integer times, accumulated delay of request j served at time tau is
# sum of d_j(u) for u in [r_j, tau); unserved requests accrue delay to
# the (finite) evaluation horizon, which understates the paper's
# tau = infinity — stated as a restriction, not a claim.

@dataclass(frozen=True)
class SCDRequest:
    rid: str
    element: str
    arrival: int
    delay: tuple  # delay[u] = momentary delay at time arrival + u (Fraction)

    def accumulated(self, tau: int) -> Fraction:
        return sum((self.delay[u] for u in range(tau - self.arrival)),
                   Fraction(0))


@dataclass(frozen=True)
class SCDInstance:
    sets: dict          # name -> frozenset of elements
    cost: dict          # name -> Fraction (>= 1)
    requests: tuple     # SCDRequest
    horizon: int


def scd_service_time(inst: SCDInstance, schedule, req):
    """schedule: iterable of (time, setname). Paper semantics: first
    purchase at time >= arrival of a set containing the element."""
    times = [t for (t, s) in schedule
             if req.element in inst.sets[s] and t >= req.arrival]
    return min(times) if times else None


def scd_objective(inst: SCDInstance, schedule):
    buying = sum((inst.cost[s] for (_, s) in schedule), Fraction(0))
    delay = Fraction(0)
    for req in inst.requests:
        tau = scd_service_time(inst, schedule, req)
        delay += req.accumulated(tau if tau is not None else inst.horizon)
    return buying, delay, buying + delay


def scd_generic_history(inst: SCDInstance, schedule):
    """The same schedule as a generic interaction history: at step t the
    action is ("buy", s) or ("wait",); the response is the tuple of
    request ids arriving at t (environment-supplied, response-irrelevant
    for service progress)."""
    buys = {t: s for (t, s) in schedule}
    hist = []
    for t in range(inst.horizon):
        action = ("buy", buys[t]) if t in buys else ("wait",)
        arrivals = tuple(r.rid for r in inst.requests if r.arrival == t)
        hist.append((action, arrivals))
    return tuple(hist)


def scd_spec(inst: SCDInstance, req: SCDRequest) -> ServiceSpec:
    """Pinned spec for one request occurrence: a certificate cites one
    purchase receipt of a covering set at a time >= arrival."""
    def check(cited, data):
        if len(cited) != 1:
            return False
        r = cited[0]
        return (r.action[0] == "buy"
                and req.element in inst.sets[r.action[1]]
                and r.index >= req.arrival)

    def make(transcript):
        for r in transcript:
            if (r.action[0] == "buy"
                    and req.element in inst.sets[r.action[1]]
                    and r.index >= req.arrival):
                return Certificate(req.rid, (r.index,))
        return None

    return ServiceSpec(req.rid, check, make)


def scd_generic_objective(inst: SCDInstance, schedule):
    """Recompute the SCD objective purely from the generic run: action
    costs from the trace, per-liability delay to the certificate's cited
    receipt."""
    hist = scd_generic_history(inst, schedule)
    transcript = transcript_of(hist)
    buying = sum((inst.cost[a[1]] for (a, _) in hist if a[0] == "buy"),
                 Fraction(0))
    delay = Fraction(0)
    service_times = {}
    for req in inst.requests:
        spec = scd_spec(inst, req)
        cert = spec.make_cert(transcript)
        if cert is not None and spec.check(transcript, cert):
            tau = cert.cited[0]
            service_times[req.rid] = tau
            delay += req.accumulated(tau)
        else:
            service_times[req.rid] = None
            delay += req.accumulated(inst.horizon)
    return buying, delay, buying + delay, service_times


# ---------------------------------------------------------------------------
# B. Submodular Ranking / Minimum Latency Submodular Cover
# ---------------------------------------------------------------------------
# Paper model: metric (V, d), root r, normalized monotone submodular
# f_i : 2^V -> [0,1]; cover time of f_i on path pi is
# min { t : f_i({v within distance t on pi}) = 1 }; objective is the sum
# of cover times. Uniform metric with distinct vertices = Submodular
# Ranking (cover time = prefix length). Repetition is harmless because
# progress factors through the visited set.

@dataclass(frozen=True)
class MLSCInstance:
    vertices: tuple
    d: dict            # (u, v) -> Fraction, symmetric
    root: str
    functions: dict    # name -> callable frozenset -> Fraction in [0,1]


def mlsc_cover_time(inst: MLSCInstance, path, fname):
    f = inst.functions[fname]
    pos, dist = inst.root, Fraction(0)
    visited = {inst.root}
    if f(frozenset(visited)) == 1:
        return Fraction(0)
    for v in path:
        dist += inst.d[(pos, v)]
        pos = v
        visited.add(v)
        if f(frozenset(visited)) == 1:
            return dist
    return None


def mlsc_objective(inst: MLSCInstance, path):
    return sum((mlsc_cover_time(inst, path, n) for n in inst.functions),
               start=Fraction(0))


def mlsc_spec(inst: MLSCInstance, fname) -> ServiceSpec:
    """Generic spec: certified when the visited set (root plus cited
    action receipts) reaches value 1. Set-factorizing by construction."""
    f = inst.functions[fname]

    def check(cited, data):
        return f(frozenset({inst.root} | {r.action for r in cited})) == 1

    def make(transcript):
        for k in range(len(transcript) + 1):
            cited = tuple(range(k))
            if f(frozenset({inst.root}
                           | {transcript[i].action for i in cited})) == 1:
                return Certificate(fname, cited)
        return None

    return ServiceSpec(fname, check, make)


def mlsc_generic_cover_times(inst: MLSCInstance, path):
    """Run the path as a generic history (response space is a
    singleton), with the metric as per-step action cost; cover time of a
    spec is the accumulated cost at first certification."""
    hist = tuple((v, "ok") for v in path)
    transcript = transcript_of(hist)
    prefix_cost = [Fraction(0)]
    pos = inst.root
    for v in path:
        prefix_cost.append(prefix_cost[-1] + inst.d[(pos, v)])
        pos = v
    out = {}
    for fname in inst.functions:
        spec = mlsc_spec(inst, fname)
        cert = spec.make_cert(transcript)
        if cert is None or not spec.check(transcript, cert):
            out[fname] = None
        else:
            out[fname] = prefix_cost[len(cert.cited)]
    return out


# ---------------------------------------------------------------------------
# C. Adaptive Submodularity (Golovin-Krause)
# ---------------------------------------------------------------------------
# Items E with states in O; realization phi : E -> O; known prior;
# selecting an item reveals its state; partial realization psi is the
# observed item->state map. Coverage (Def 7, quota form): after psi,
# f(dom psi, phi') >= Q for EVERY realization phi' consistent with psi.
# That is the learner-visible certificate. Semantic success -- quota
# under the true realization only -- needs the hidden state and is NOT
# core structure. Self-certifying (Def 8): semantic success at the true
# realization implies the certificate.

@dataclass(frozen=True)
class GKInstance:
    items: tuple
    realizations: dict   # name -> dict item -> state
    prior: dict          # name -> Fraction, positive, sums to 1
    f: object            # callable (frozenset items, name) -> Fraction
    quota: Fraction


def gk_psi(history):
    return {a: y for (a, y) in history}


def gk_consistent(inst: GKInstance, phi_name, psi: dict) -> bool:
    phi = inst.realizations[phi_name]
    return all(phi[e] == s for e, s in psi.items())


def gk_env(inst: GKInstance) -> Env:
    def responses(history, item):
        psi = gk_psi(history)
        return frozenset(inst.realizations[n][item]
                         for n in inst.realizations
                         if gk_consistent(inst, n, psi))
    return Env(inst.items, responses)


def gk_certified(inst: GKInstance, history) -> bool:
    """GK Definition 7 (quota form): the record-visible certificate."""
    psi = gk_psi(history)
    dom = frozenset(psi)
    names = [n for n in inst.realizations if gk_consistent(inst, n, psi)]
    return bool(names) and all(inst.f(dom, n) >= inst.quota for n in names)


def gk_semantic(inst: GKInstance, history, true_name) -> bool:
    """Quota under the true realization only: analytic, not core."""
    return inst.f(frozenset(gk_psi(history)), true_name) >= inst.quota


def gk_self_certifying(inst: GKInstance) -> bool:
    """GK Definition 8, specialized to the quota objective: for every
    reachable psi and consistent phi, phi', quota at phi iff quota at
    phi'. Checked exhaustively over all item subsets as domains."""
    for k in range(len(inst.items) + 1):
        for dom in itertools.combinations(inst.items, k):
            for n1 in inst.realizations:
                psi = {e: inst.realizations[n1][e] for e in dom}
                names = [n for n in inst.realizations
                         if gk_consistent(inst, n, psi)]
                vals = [inst.f(frozenset(dom), n) >= inst.quota
                        for n in names]
                if any(vals) and not all(vals):
                    return False
    return True


def gk_delta(inst: GKInstance, item, psi: dict) -> Fraction:
    """Conditional expected marginal benefit (GK Definition 1)."""
    names = [n for n in inst.realizations if gk_consistent(inst, n, psi)]
    mass = sum((inst.prior[n] for n in names), Fraction(0))
    dom = frozenset(psi)
    num = sum((inst.prior[n]
               * (inst.f(dom | {item}, n) - inst.f(dom, n))
               for n in names), Fraction(0))
    return num / mass


def gk_adaptive_submodular(inst: GKInstance) -> bool:
    """GK Definition 3, checked exhaustively over subrealization pairs
    psi subseteq psi' arising from realizations in the support."""
    doms = [frozenset(c) for k in range(len(inst.items) + 1)
            for c in itertools.combinations(inst.items, k)]
    for n in inst.realizations:
        phi = inst.realizations[n]
        for d1 in doms:
            for d2 in doms:
                if not d1 <= d2:
                    continue
                psi1 = {e: phi[e] for e in d1}
                psi2 = {e: phi[e] for e in d2}
                for e in inst.items:
                    if e in d2:
                        continue
                    if gk_delta(inst, e, psi1) < gk_delta(inst, e, psi2):
                        return False
    return True


# ---------------------------------------------------------------------------
# D. Interactive Submodular Set Cover (Guillory-Bilmes)
# ---------------------------------------------------------------------------
# Finite hypothesis class H with unknown target h*; questions q with
# known nonempty valid-response sets q(h); responses adversarial but
# consistent with h*; objective functions F_h over question-response
# pairs, monotone submodular; goal F_{h*}(S) >= alpha. The stated
# termination references the true h*; the learner-visible certificate is
# the version-space-uniform statement: F_h(S) >= alpha for every h still
# consistent.

@dataclass(frozen=True)
class ISSCInstance:
    hypotheses: tuple
    questions: tuple
    valid: dict          # (q, h) -> frozenset of responses, nonempty
    cost: dict           # q -> Fraction
    F: dict              # h -> callable frozenset[(q, r)] -> Fraction
    alpha: Fraction


def issc_version_space(inst: ISSCInstance, history):
    return [h for h in inst.hypotheses
            if all(r in inst.valid[(q, h)] for (q, r) in history)]


def issc_env(inst: ISSCInstance) -> Env:
    def responses(history, q):
        vs = issc_version_space(inst, history)
        return frozenset(r for h in vs for r in inst.valid[(q, h)])
    return Env(inst.questions, responses)


def issc_certified(inst: ISSCInstance, history) -> bool:
    pairs = frozenset(history)
    vs = issc_version_space(inst, history)
    return bool(vs) and all(inst.F[h](pairs) >= inst.alpha for h in vs)


def issc_semantic(inst: ISSCInstance, history, target) -> bool:
    return inst.F[target](frozenset(history)) >= inst.alpha


def issc_fixed_target_witness(inst: ISSCInstance, history) -> bool:
    """The consistency-adversary = fixed-target lemma, as a finite
    check: every response in the run was permitted by every hypothesis
    in the final version space, so any of them, fixed in advance, would
    have permitted the entire run."""
    vs = issc_version_space(inst, history)
    return all(r in inst.valid[(q, h)] for h in vs for (q, r) in history)


# ---------------------------------------------------------------------------
# E. Request-Response games (Horn-Thomas-Wallmeier-Zimmermann)
# ---------------------------------------------------------------------------
# Arena (V, V0, V1, E), conditions (Q_j, P_j); a play is winning for
# Player 0 if every visit to Q_j is followed by a later (or equal) visit
# to P_j. Waiting time wt_j per the paper's inductive definition; while
# a request is open, additional same-type requests are IGNORED
# (coalesced). Value of a play: limsup of mean accumulated penalties.

@dataclass(frozen=True)
class RRGame:
    vertices: tuple
    edges: dict          # v -> tuple of successors
    owner: dict          # v -> 0 or 1
    conditions: tuple    # ((Qset, Pset), ...)


def rr_wt_step(game: RRGame, j, wt, v):
    q, p = game.conditions[j]
    if wt == 0:
        return 1 if (v in q and v not in p) else 0
    return 0 if v in p else wt + 1


def rr_wt_vector(game: RRGame, prefix):
    wt = [0] * len(game.conditions)
    for v in prefix:
        wt = [rr_wt_step(game, j, wt[j], v) for j in range(len(wt))]
    return tuple(wt)


def rr_value_periodic(game: RRGame, stem, cycle):
    """Exact value of the ultimately periodic play stem . cycle^omega
    with identity penalty functions: limsup of mean accumulated
    penalties. The (cycle position, wt vector) pair eventually repeats;
    the value is the mean of p over that repeating block (the limsup and
    limit agree because the sequence of penalties is ultimately
    periodic). Diverges (returns None) if some wt grows without bound,
    detected by exceeding a bound that forces growth."""
    wt = [0] * len(game.conditions)
    for v in stem:
        wt = [rr_wt_step(game, j, wt[j], v) for j in range(len(wt))]
    seen = {}
    penalties = []
    pos = 0
    bound = (len(stem) + len(cycle)) * 4 + 64
    while True:
        key = (pos, tuple(wt))
        if key in seen:
            start = seen[key]
            block = penalties[start:]
            return sum(block, Fraction(0)) / len(block)
        seen[key] = len(penalties)
        v = cycle[pos]
        wt = [rr_wt_step(game, j, wt[j], v) for j in range(len(wt))]
        penalties.append(sum((Fraction(w) for w in wt), Fraction(0)))
        if any(w > bound for w in wt):
            return None
        pos = (pos + 1) % len(cycle)


def rr_play_winning(game: RRGame, stem, cycle) -> bool:
    """RR condition on an ultimately periodic play. A request open
    forever makes its waiting time diverge, so with identity penalties
    the play is winning iff its value is finite: on a winning play the
    (cycle position, wt vector) pair is eventually periodic, because a
    positive wt that never resets across a repeated block would have to
    grow across it."""
    return rr_value_periodic(game, stem, cycle) is not None


# Occurrence-level accounting for the same play: mint one liability per
# OPENING event (coalescing: a Q_j visit while open mints nothing), and
# check certified service per occurrence.

def rr_occurrences(game: RRGame, prefix):
    """(condition j, opening time, closing time or None) per coalesced
    occurrence along a finite play prefix."""
    out = []
    open_at = {}
    for t, v in enumerate(prefix):
        for j, (q, p) in enumerate(game.conditions):
            if j in open_at and v in p:
                out.append((j, open_at.pop(j), t))
            elif j not in open_at and v in q and v not in p:
                open_at[j] = t
    for j, t0 in open_at.items():
        out.append((j, t0, None))
    return out
