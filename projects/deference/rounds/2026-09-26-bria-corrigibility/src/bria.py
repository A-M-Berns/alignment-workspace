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
                drill: Optional[Callable[[str], Q]] = None):
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
        G = rescale(P, N, resid)
        b = rescale(P, N, bid)
        h.wealth += wk * (G - b)
        h.record += wk * (G - b)
        log.append(dict(block=k, winner=h.name, cont=cname, bid=bid, resid=resid,
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
