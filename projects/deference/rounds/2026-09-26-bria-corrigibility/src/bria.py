"""The lexical Continuation BRIA design on realized scores: the evaluation, the two
settlement conventions, the opening-subsidy auction settled on the realized lexical score,
the helper attribution rule, the consultation model extended with covert influence on her
standards and a raise dimension, criteria anchored at the decision, and the three
evaluation-timing options.  Exact rationals throughout."""

from dataclasses import dataclass, field, replace
from fractions import Fraction as Q
from typing import Callable, Dict, List, Optional, Tuple


# ----------------------------------------------------------------------------- the design

@dataclass(frozen=True)
class Lex:
    D: Q
    w: Q
    varpi: Q

    def __post_init__(self):
        assert self.w <= 0 <= self.D < self.varpi and self.D - self.varpi < self.w


def realized(P: Lex, gord: Q, n_known: int, n_fore: int, n_late: int) -> Q:
    """The realized lexical score of a block."""
    return gord - P.varpi * (n_known + n_fore + n_late)


def eval_of(P: Lex, bid: Q, n_known: int, pS: Q, pT: Q) -> Q:
    """The agent's evaluation of a continuation."""
    return bid - P.varpi * n_known - P.varpi * (pS + pT)


def resid_i(P: Lex, gord: Q, n_late: int) -> Q:
    """Convention (i): realized forecast-class violations added back."""
    return gord - P.varpi * n_late


def resid_ii(P: Lex, gord: Q, n_fore: int, n_late: int, pS: Q, pT: Q) -> Q:
    """Convention (ii): the prices added back."""
    return gord - P.varpi * n_late - P.varpi * n_fore + P.varpi * (pS + pT)


def rescale(P: Lex, N: int, s: Q) -> Q:
    lo = P.w - P.varpi * N
    return (s - lo) / (P.D - lo)


def implied_threshold(P: Lex, bid: Q) -> Q:
    return (bid - P.w) / P.varpi


# ----------------------------------------------------------------------------- the auction

@dataclass
class Hypothesis:
    name: str
    bid_of: Callable[[str, int], Optional[Q]]   # continuation, block -> bid on the residual, or None
    wealth: Q = Q(0)
    record: Q = Q(0)


@dataclass
class Continuation:
    name: str
    n_known: int
    pS: Q
    pT: Q
    gord: Q                 # her realized gated ordinary evaluation of the block
    n_fore: int             # forecast-class violations realized
    n_late: int             # violations detected only after the fact (own steps)
    helper: Tuple[Tuple[int, int], ...] = ()   # (detection delay, count) of helper violations
    is_inquiry: bool = False


def attributed(own: int, helper, k: int, H: int) -> int:
    return own + sum(c for d, c in helper if d <= k + H)


def run_auction(P: Lex, hyps: List[Hypothesis], menu: Dict[str, Continuation], blocks: int,
                allowance: Callable[[int, str], Q], weight: Callable[[int], Q],
                convention: str = "ii", horizon: int = 0, N: int = 2,
                drill: Optional[Callable[[str], Q]] = None,
                noise: Optional[Callable[[int], Q]] = None):
    """The opening-subsidy auction on the composed gate's support, the winner maximizing the
    lexical evaluation among feasible bids, settled on the rescaled realized residual under
    the named convention.  Returns the per-block log."""
    log = []
    for k in range(blocks):
        wk = weight(k)
        for h in hyps:
            h.wealth += allowance(k, h.name)
        best = None
        for h in hyps:
            for cname, c in menu.items():
                bid = h.bid_of(cname, k)
                if bid is None:
                    continue
                bid = min(bid, P.D)
                # opening-timing feasibility, in rescaled units
                if wk * rescale(P, N, bid) > h.wealth:
                    continue
                pS = c.pS if drill is None else drill(cname)
                ev = eval_of(P, bid, c.n_known, pS, c.pT)
                key = (ev, c.is_inquiry)          # ties go to inquiry
                if best is None or key > best[0]:
                    best = (key, h, cname, bid, pS)
        if best is None:
            raise RuntimeError(f"no feasible bid at block {k}: the allowance does not cover the "
                               "rescaled window bid of the default bidder")
        _, h, cname, bid, pS = best
        c = menu[cname]
        n_late = c.n_late + attributed(0, c.helper, 0, horizon)
        if convention == "ii":
            resid = resid_ii(P, c.gord, c.n_fore, n_late, pS, c.pT)
        else:
            resid = resid_i(P, c.gord, n_late)
        m_resid = resid
        xi = noise(k) if noise is not None else Q(0)
        resid = m_resid + xi                                   # realized = expected + noise
        G = rescale(P, N, resid)
        b = rescale(P, N, bid)
        h.wealth += wk * (G - b)
        h.record += wk * (G - b)
        log.append(dict(block=k, winner=h.name, cont=cname, bid=bid, resid=resid, m=m_resid,
                        xi=xi, G=G, b=b,
                        realized=realized(P, c.gord, c.n_known, c.n_fore, n_late)))
    return log


def argmax_chooser(estimates: Dict[str, Q]) -> str:
    return max(estimates, key=lambda a: estimates[a])


# ----------------------------------------------------------------------------- the model

@dataclass(frozen=True)
class Decl:
    convention: str = "neutral"
    raise_trigger: bool = False


@dataclass(frozen=True)
class Pres:
    framing: str
    recommend: bool
    raise_: bool


def present(policy: str, d: Decl, w: bool) -> Pres:
    if policy == "honest":
        return Pres(d.convention, w, d.raise_trigger)
    if policy == "frameByWant":
        return Pres("slant" + str(w), w, d.raise_trigger)
    if policy == "slantTrue":
        return Pres("slantTrue", w, d.raise_trigger)
    if policy == "raiseByWant":
        return Pres(d.convention, w, w)
    if policy == "raiseDeclared":
        return Pres(d.convention, w, d.raise_trigger)
    raise ValueError(policy)


@dataclass(frozen=True)
class Model:
    decl: Decl
    policies: Tuple[str, ...]
    prog: bool                       # her own verdict
    influence: Optional[Tuple[str, bool]] = None    # (who, implanted verdict)
    disclosed_at: Optional[int] = None


def eff_prog(M: Model) -> bool:
    return M.influence[1] if M.influence else M.prog


def transparent(M: Model, crit: Decl, i: int) -> bool:
    """The agent's contribution at round `i` equals the reference computed from the
    declared inputs under `crit`, for every wanted answer."""
    for w in (False, True):
        p = present(M.policies[i], M.decl, w)
        if p.framing != crit.convention or p.raise_ != crit.raise_trigger:
            return False
    return True


def authored(M: Model, i: int) -> bool:
    """Her verdict at round `i` is licensed by the grounds: her effective program's own
    verdict, and — if her standards were influenced — the influence disclosed by then."""
    if M.influence is not None and (M.disclosed_at is None or M.disclosed_at > i):
        return False
    return True


def counted(M: Model, crit: Decl, i: int) -> bool:
    """The segment of round `i` alone."""
    return transparent(M, crit, i) and authored(M, i)


def missed_disclosure(M: Model, i: int) -> bool:
    return (M.influence is not None and M.influence[0] == "agent"
            and (M.disclosed_at is None or M.disclosed_at > i))


def crit_at(d0: Decl, amendments: List[Tuple[int, Decl]], t: int) -> Decl:
    live = [d for (s, d) in amendments if s <= t]
    return live[-1] if live else d0


def crit_latest(d0: Decl, amendments: List[Tuple[int, Decl]]) -> Decl:
    return amendments[-1][1] if amendments else d0


def gated(counted_: bool, ord_: Q, w: Q) -> Q:
    return ord_ if counted_ else w


def conditioned(ord_: Q) -> Q:
    return ord_


# ----------------------------------------------------------------------------- timing

def weights_deterministic(T: int, f_n: int) -> List[Q]:
    return [Q(1) if t == f_n else Q(0) for t in range(T)]


def weights_geometric(T: int, q: Q, start: int) -> List[Q]:
    raw = [Q(0)] * start + [(1 - q) ** (t - start) * q for t in range(start, T)]
    s = sum(raw)
    return [r / s for r in raw]


def mix_score(alpha: List[Q], U: List[Q]) -> Q:
    return sum(a * u for a, u in zip(alpha, U))


def harmed(base: Q, h: Q, n: int, d: int, T: int) -> List[Q]:
    return [base - (h if n + d <= t else Q(0)) for t in range(T)]


def tail_weight(alpha: List[Q], s: int) -> Q:
    return sum(a for t, a in enumerate(alpha) if t >= s)


def partial_settlement(alpha: List[Q], U: List[Q], settled: set) -> Tuple[Q, Q]:
    part = sum(alpha[t] * U[t] for t in settled)
    remaining = sum(alpha[t] for t in range(len(alpha)) if t not in settled)
    return part, remaining


# ----------------------------------------------------------------------------- follow-up

def taint_after(reads: Dict[str, set], writes: Dict[str, set], steps) -> set:
    """Taint tracked through state components: a violating act taints its writes, an act
    reading taint taints its writes, a remedy clears.  `steps` are ('act', name, viol) or
    ('remedy',)."""
    T: set = set()
    for s in steps:
        if s[0] == "remedy":
            T = set()
        else:
            _, a, viol = s
            if viol or (reads[a] & T):
                T = T | writes[a]
    return T


def uses(reads: Dict[str, set], T: set, a: str) -> bool:
    return bool(reads[a] & T)


def standing_record(P: Lex, bids: List[Q], gords: List[Q], used: List[bool]) -> Q:
    """Net record over blocks: a block using tracked fruits carries a count of one."""
    return sum((resid_i(P, g, 1 if u else 0) - b) for b, g, u in zip(bids, gords, used))


def signed_margin(log, weights, incident: Callable[[dict], bool]) -> Tuple[Q, Q]:
    """(signed margin, positive-part margin) over non-incident blocks of an auction log."""
    signed = sum(weights(e["block"]) * (e["G"] - e["b"]) for e in log if not incident(e))
    pos = sum(weights(e["block"]) * max(e["G"] - e["b"], Q(0)) for e in log if not incident(e))
    return signed, pos


def landed_allowance_total(m: List[int]) -> Q:
    """The landed prefix rule's total subsidy bound `2√(S_K M_K) + √S_K (1 + ln K)`, as the
    exact per-block rule `(M_k − M_{k−1}) + 1/k` summed over the active frontier
    `s(k) = ⌊√(S_k/M_k)⌋`."""
    import math
    S, M, total = 0, 0, Q(0)
    for k, mk in enumerate(m, start=1):
        S += mk
        Mprev = M
        M = max(M, mk)
        s = int(math.isqrt(S // M)) if M else 0
        total += s * (Q(M - Mprev) + Q(1, k))
    return total


def run_delayed_auction(P: Lex, hyps: List[Hypothesis], menu: Dict[str, Continuation],
                        blocks: int, allowance, weight, lag: Callable[[int], int], N: int = 2):
    """The auction with block `k` settled at `k + L_k`; bids feasible against cash net of
    escrow.  Returns the log and the cash history."""
    log, pending, cash_hist = [], [], []
    for h in hyps:
        h.wealth = Q(0)
    for k in range(blocks):
        # settle what is due
        due = [p for p in pending if p["settle_at"] <= k]
        pending = [p for p in pending if p["settle_at"] > k]
        for p in due:
            p["hyp"].wealth += p["w"] * p["G"]
        wk = weight(k)
        for h in hyps:
            h.wealth += allowance(k, h.name)
        best = None
        for h in hyps:
            for cname, c in menu.items():
                bid = h.bid_of(cname, k)
                if bid is None:
                    continue
                bid = min(bid, P.D)
                if wk * rescale(P, N, bid) > h.wealth:       # cash is net of escrow already
                    continue
                ev = eval_of(P, bid, c.n_known, c.pS, c.pT)
                key = (ev, c.is_inquiry)
                if best is None or key > best[0]:
                    best = (key, h, cname, bid)
        if best is None:
            raise RuntimeError(f"no feasible bid at block {k}")
        _, h, cname, bid = best
        c = menu[cname]
        resid = resid_ii(P, c.gord, c.n_fore, c.n_late, c.pS, c.pT)
        G, b = rescale(P, N, resid), rescale(P, N, bid)
        h.wealth -= wk * b                                    # escrow the bid now
        pending.append(dict(hyp=h, w=wk, G=G, settle_at=k + lag(k)))
        log.append(dict(block=k, winner=h.name, cont=cname, G=G, b=b))
        cash_hist.append({hh.name: hh.wealth for hh in hyps})
    return log, cash_hist, len(pending)


def drilled_price(true_freq: Q, market_p: Q, q: Q, blocks: int, seed: int = 7) -> List[Q]:
    """A toy inductor whose price on the chosen path moves toward the drilled frequency: at
    each drilled block (rate q) the price is updated by the settled outcome; undrilled
    blocks give no feedback.  Deterministic pseudo-random schedule."""
    import random
    rng = random.Random(seed)
    p, out, seen, shorts = market_p, [], 0, 0
    for k in range(blocks):
        out.append(p)
        if rng.random() < float(q):
            seen += 1
            shorts += 1 if rng.random() < float(true_freq) else 0
            p = Q(shorts, seen)
    return out


# ----------------------------------------------------------------------------- follow-up 2

def taint_after2(reads: Dict[str, set], writes: Dict[str, set], steps) -> set:
    """Per-violation taint: a set of (violation, component) pairs.  A violating act taints its
    writes with its own identifier; an act reading tainted components taints its writes with
    every violation read (taint joins at reads); `('remedy', v)` clears `v`'s taint only.
    `steps` are ('act', name, violation-id-or-None) or ('remedy', violation-id)."""
    T: set = set()
    for s in steps:
        if s[0] == "remedy":
            T = {p for p in T if p[0] != s[1]}
        else:
            _, a, viol = s
            read = {v for (v, c) in T if c in reads[a]}
            if viol is not None:
                read = read | {viol}
            T = T | {(v, d) for v in read for d in writes[a]}
    return T


def uses2(reads: Dict[str, set], T: set, a: str) -> bool:
    return any(c in reads[a] for (_, c) in T)


def tainted_by(T: set, c: str) -> set:
    return {v for (v, cc) in T if cc == c}


def detect_at(steps, k0: int, v):
    """Detection relabels the commission step at position `k0` with the violation's id."""
    out = list(steps)
    if k0 < len(out) and out[k0][0] == "act":
        out[k0] = ("act", out[k0][1], v)
    return out


def standing_record_ii(P: Lex, bids: List[Q], gords: List[Q], counts: List[Tuple[int, int, int]],
                       prices: List[Tuple[Q, Q]]) -> Q:
    """Net record under convention (ii): per block `residII − bid` with the block's counts
    (n_known, n_fore, n_late) and prices (pS, pT)."""
    return sum((resid_ii(P, g, nf, nl, pS, pT) - b)
               for b, g, (nk, nf, nl), (pS, pT) in zip(bids, gords, counts, prices))


def greedy_debit(A: List[Q], C: Q) -> List[Q]:
    """The greedy debit schedule of a charge `C` against an allowance stream `A`."""
    out, taken = [], Q(0)
    for a in A:
        d = min(a, max(Q(0), C - taken))
        out.append(d)
        taken += d
    return out


def run_window_auction(P: Lex, hyps: List[Hypothesis], menu: Dict[str, Continuation], blocks: int,
                       allowance, weight, reads: Dict[str, set], writes: Dict[str, set],
                       commit_block: int, detect_block: int, N: int = 2):
    """The auction with a standing violation committed at `commit_block` and detected at
    `detect_block`.  Before detection blocks are settled as chosen, with no taint on record.
    At detection the commission step is flagged, the taint is recomputed over the record from
    commission, and every settled block whose continuation committed or used the fruits is
    debited `ϖ` (rescaled) against its winner's future allowance by the greedy schedule.  From
    detection on, use of a tainted component is compiled into `n_known`.  Returns the log, the
    per-hypothesis collected debits, and the outstanding debits."""
    unit = rescale(P, N, Q(0)) - rescale(P, N, -P.varpi)   # ϖ in rescaled units
    log, record = [], []
    outstanding = {h.name: Q(0) for h in hyps}
    collected = {h.name: Q(0) for h in hyps}
    T: set = set()
    for k in range(blocks):
        wk = weight(k)
        for h in hyps:
            A = allowance(k, h.name)
            d = min(A, outstanding[h.name])
            outstanding[h.name] -= d
            collected[h.name] += d
            h.wealth += A - d
        detected = k >= detect_block
        if k == detect_block:
            flagged = detect_at(record, commit_block, "v")
            for e in log:
                prefix = taint_after2(reads, writes, flagged[:e["block"]])
                step = flagged[e["block"]]
                if step[2] is not None or uses2(reads, prefix, e["cont"]):
                    outstanding[e["winner"]] += e["w"] * unit
                    e["debit"] = e["w"] * unit
            T = taint_after2(reads, writes, flagged)
        best = None
        for h in hyps:
            for cname, c in menu.items():
                bid = h.bid_of(cname, k)
                if bid is None:
                    continue
                bid = min(bid, P.D)
                if wk * rescale(P, N, bid) > h.wealth:
                    continue
                n_known = c.n_known + (1 if detected and uses2(reads, T, cname) else 0)
                ev = eval_of(P, bid, n_known, c.pS, c.pT)
                key = (ev, c.is_inquiry)
                if best is None or key > best[0]:
                    best = (key, h, cname, bid, n_known)
        if best is None:
            raise RuntimeError(f"no feasible bid at block {k}")
        _, h, cname, bid, n_known = best
        c = menu[cname]
        resid = resid_ii(P, c.gord, c.n_fore, c.n_late, c.pS, c.pT)
        G, b = rescale(P, N, resid), rescale(P, N, bid)
        h.wealth += wk * (G - b)
        record.append(("act", cname, None))
        if detected:
            T = taint_after2(reads, writes, detect_at(record, commit_block, "v"))
        log.append(dict(block=k, winner=h.name, cont=cname, w=wk, G=G, b=b, n_known=n_known,
                        debit=Q(0)))
    return log, collected, outstanding


def random_locked(alpha: List[Q], bid: Q, t: int) -> Q:
    """Expected locked capital under a random time `T ~ alpha`: `E[bid · 1[T > t]]`."""
    return sum(a * (bid if t < s else Q(0)) for s, a in enumerate(alpha))


def mixture_locked(alpha: List[Q], bid: Q, t: int) -> Q:
    """Locked capital under the mixture settled in pieces: the bid less the released shares."""
    return bid - sum(a * bid for s, a in enumerate(alpha) if s <= t)


def average_of_k_draws(alpha: List[Q], U: List[Q], k: int) -> Tuple[Q, Q]:
    """Exact mean and variance of the average of `k` independent draws from `alpha`, scored by
    `U`, by enumerating the product distribution."""
    from itertools import product
    mean, second = Q(0), Q(0)
    for ts in product(range(len(alpha)), repeat=k):
        p = Q(1)
        for t in ts:
            p *= alpha[t]
        if p == 0:
            continue
        s = sum(U[t] for t in ts) / k
        mean += p * s
        second += p * s * s
    return mean, second - mean * mean


def evaluation_load(option: str, support: int = 0, k: int = 1) -> int:
    """Her evaluations per decision: option 1 one at a public time; option 2 one per time in
    the support; option 3 one at a hidden time; option 4 `k` at hidden times."""
    return {"deterministic": 1, "mixture": support, "random": 1, "hybrid": k}[option]


# ----------------------------------------------------------------------------- follow-up 3

def pm_noise(seed: int, amplitude: Q) -> Callable[[int], Q]:
    """Deterministic ±amplitude noise from a linear congruential generator on the seed: the
    same run every time, exact rationals."""
    def xi(k: int) -> Q:
        state = (1103515245 * (seed + 7919 * k) + 12345) % (2 ** 31)
        state = (1103515245 * state + 12345) % (2 ** 31)
        return amplitude if (state >> 16) & 1 else -amplitude
    return xi


def isqrt_upper(n: int) -> int:
    """An integer upper bound on √n."""
    import math
    r = math.isqrt(n)
    return r if r * r == n else r + 1


def noise_bound(K: int, amplitude: Q) -> Q:
    """A rational majorant of the Azuma–Hoeffding scale `amplitude · √(2 K ln(2K))`, using
    `ln x ≤ bit_length(x)`: exact, monotone in `K`, and `o(K)`."""
    if K == 0:
        return Q(0)
    return amplitude * isqrt_upper(2 * K * (2 * K).bit_length())


def tracker_schedule(wbar_D: Q, eps: Callable[[int], Q], M: Callable[[int], Q]) -> Callable[[int], Q]:
    """The tracker's minimal allowance under noise: `w̄·D + M(0)` at entry, then the honest
    loss plus the increment of the noise bound (`trackerAllowance2`)."""
    def A(k: int) -> Q:
        if k == 0:
            return wbar_D + M(0)
        return eps(k - 1) + (M(k) - M(k - 1))
    return A
