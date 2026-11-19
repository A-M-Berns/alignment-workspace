"""Exact checks behind RESULTS.md and NEGATIVE_RESULTS.md.  CHECKS: statement id -> function
returning {'supports': status, ...facts}.  A proof is on paper in the documents; a check of a
proved statement recomputes it on seeded random finite cases and fails loudly on a miss."""
from __future__ import annotations

import itertools
import random
from fractions import Fraction as F

PROVED, EXAMPLE, REFUTED = "proved", "holds on the stated example", "refuted"


def rnd_law(rng, n):
    w = [rng.randint(1, 9) for _ in range(n)]
    return [F(x, sum(w)) for x in w]


def cond(p, vals, key):
    """E[vals | key] as a list over states."""
    agg = {}
    for pi, v, k in zip(p, vals, key):
        w, t = agg.get(k, (F(0), F(0)))
        agg[k] = (w + pi, t + pi * v)
    return [agg[k][1] / agg[k][0] for k in key]


def E(p, vals):
    return sum((pi * v for pi, v in zip(p, vals)), F(0))


def c1():
    rng = random.Random(61)
    for _ in range(400):
        n = rng.randint(2, 7)
        p = rnd_law(rng, n)
        X = [F(rng.randint(0, 6), 3) for _ in range(n)]
        x = [F(rng.randint(0, 3), 2) for _ in range(n)]
        I = [rng.randint(0, 2) for _ in range(n)]
        m = E(p, [(a - b) ** 2 for a, b in zip(x, cond(p, X, list(zip(x, I))))])
        m0 = E(p, [(a - b) ** 2 for a, b in zip(x, cond(p, X, x))])
        assert (E(p, x) - E(p, X)) ** 2 <= m0 <= m
        # the split of expected squared error
        assert E(p, [(a - b) ** 2 for a, b in zip(x, X)]) == m0 + E(p, [(a - b) ** 2 for a, b in zip(cond(p, X, x), X)])
    return {"supports": PROVED, "cases": 400}


def c2():
    rng = random.Random(62)
    for _ in range(400):
        n = rng.randint(2, 8)
        p = rnd_law(rng, n)
        X = [F(rng.randint(0, 6), 3) for _ in range(n)]
        x = [F(rng.randint(0, 3), 2) for _ in range(n)]
        Fi = [rng.randint(0, 2) for _ in range(n)]
        own = cond(p, X, Fi)
        both = cond(p, X, list(zip(x, Fi)))
        now = E(p, [(a - b) ** 2 for a, b in zip(own, X)])
        defer = E(p, [(a - b) ** 2 for a, b in zip(x, X)])
        assert now - defer == E(p, [(a - b) ** 2 for a, b in zip(both, own)]) - E(p, [(a - b) ** 2 for a, b in zip(x, both)])
    return {"supports": PROVED, "cases": 400}


def _c3_case(rng, coarse=False):
    n, k = rng.randint(2, 6), rng.randint(2, 4)
    p = rnd_law(rng, n)
    info = [rng.randint(0, 2) for _ in range(n)]
    ref_key = [i % 2 for i in info] if coarse else info
    Ustar = [[F(rng.randint(-4, 4), 2) for _ in range(n)] for _ in range(k)]
    by_info = {}
    for i in info:
        by_info.setdefault(i, ([F(rng.randint(-4, 4), 2) for _ in range(k)], rng.randrange(k)))
    u = [[by_info[info[s]][0][a] for s in range(n)] for a in range(k)]
    c = [by_info[info[s]][1] for s in range(n)]
    ubar = [cond(p, Ustar[a], ref_key) for a in range(k)]
    loss = E(p, [max(ubar[a][s] for a in range(k)) - ubar[c[s]][s] for s in range(n)])
    R = E(p, [max(u[a][s] for a in range(k)) - u[c[s]][s] for s in range(n)])
    M = sum((E(p, [(u[a][s] - ubar[a][s]) ** 2 for s in range(n)]) for a in range(k)), F(0))
    true_loss = E(p, [max(ubar[a][s] for a in range(k)) - Ustar[c[s]][s] for s in range(n)])
    return loss, R, M, true_loss


def c3():
    rng = random.Random(63)
    for _ in range(600):
        loss, R, M, true_loss = _c3_case(rng)
        d = loss - R
        assert d <= 0 or d * d <= 2 * M          # E[loss] <= E[R] + sqrt(2M), hence <= E[R] + 2 sqrt(M)
        assert true_loss == loss                 # her choice is a function of her information
    return {"supports": PROVED, "cases": 600}


def c3_tight():
    # two moves; ubar = (2e, 0); u = (e, e); she takes the second: loss 2e, R 0, M 2e^2
    e = F(1, 3)
    loss, R, M = 2 * e, F(0), 2 * e * e
    assert (loss - R) ** 2 == 2 * M
    return {"supports": EXAMPLE, "loss": loss, "R": R, "M": M, "constant": "sqrt 2, attained"}


def c3_weaker():
    rng = random.Random(64)
    for _ in range(600):
        loss, R, M, _ = _c3_case(rng, coarse=True)
        d = loss - R
        assert d <= 0 or d * d <= 2 * M
    return {"supports": PROVED, "cases": 600}


def c3_choice():
    """Refuted: C3 bounds her loss in true utility whatever her choice depends on.  Two states
    at 1/2, two moves; U* = (1, 0) at s1 and (0, 1) at s2; her information is trivial, u = ubar
    = (1/2, 1/2); her choice is the worse move at each state (it depends on the state).  The
    same scene refutes 1.5 read as a bound on true utility: the reference is coarser than what
    her choice uses."""
    p = [F(1, 2), F(1, 2)]
    Ustar = [[F(1), F(0)], [F(0), F(1)]]                 # Ustar[a][state]
    info = [0, 0]
    ubar = [cond(p, Ustar[a], info) for a in (0, 1)]
    u = ubar
    c = [1, 0]
    R = E(p, [max(u[a][s] for a in (0, 1)) - u[c[s]][s] for s in (0, 1)])
    M = sum((E(p, [(u[a][s] - ubar[a][s]) ** 2 for s in (0, 1)]) for a in (0, 1)), F(0))
    ref_loss = E(p, [max(ubar[a][s] for a in (0, 1)) - ubar[c[s]][s] for s in (0, 1)])
    true_loss = E(p, [max(ubar[a][s] for a in (0, 1)) - Ustar[c[s]][s] for s in (0, 1)])
    assert (R, M, ref_loss, true_loss) == (F(0), F(0), F(0), F(1, 2))
    return {"supports": REFUTED, "true loss": true_loss, "E[R]": R, "M": M}


def c4():
    for d0 in (F(1, 4), F(1, 2), F(1), F(2)):
        for vh in (F(0), F(1, 4), F(1, 2), F(3, 4), F(1)):
            thr = (1 - vh) / (1 + d0)
            for k in range(0, 41):
                p = F(k, 40)
                best_departure = (1 - p) * 1 + p * (-d0)        # undetected verdict at most 1
                assert (best_departure > vh) == (p < thr)
                if p >= 1 / (1 + d0):
                    assert best_departure <= vh
    return {"supports": PROVED}


def c4_score():
    """Refuted as stated: 'right on average under honest conduct' does not make the honest
    optimum's expected score the expected true utility.  Two options worth 1/2 each; her honest
    verdict is 1/2 + e, e = +-1/4 at even odds, independent; the adviser reports honestly and
    takes the option with the larger verdict."""
    score = F(0)
    for e1 in (1, -1):
        for e2 in (1, -1):
            score += F(1, 4) * (F(1, 2) + F(max(e1, e2), 4))
    assert score == F(5, 8) and F(1, 2) + F(0) == F(1, 2)        # mean verdict on a random option = 1/2
    return {"supports": REFUTED, "expected score": score, "expected true utility": F(1, 2)}


def c4_violation():
    for d0, lam in ((F(1, 2), F(2)), (F(1), F(3)), (F(1, 4), F(3, 2))):
        assert lam > 1 + d0
        for vh in (F(0), F(1, 2), F(1)):
            thr = (1 - vh) / (1 + d0 + lam)
            assert thr < F(1, 2)
            for k in range(0, 41):
                p = F(k, 40)
                assert ((1 - p) + p * (-d0 - lam) > vh) == (p < thr)
    return {"supports": PROVED}


def c4_sophisticated():
    """Two states of the adviser's knowledge, the outcome worth 1 (good) or 0 (bad), even odds;
    two messages; she knows the reporting policy and her verdict is the posterior mean.  Every
    deterministic policy: E[V] = E[U*].  With no detection the policies from which no state
    gains by sending the other message are exactly the uninformative ones.  With detection at
    p >= 1/(1 + d0) of a false report, truthful reporting is one too."""
    policies = list(itertools.product("ab", repeat=2))           # message at (good, bad)
    stable, facts = [], {}
    for pol in policies:
        post = {}
        for msg in "ab":
            states = [i for i in (0, 1) if pol[i] == msg]
            post[msg] = F(sum(1 - i for i in states), len(states)) if states else None
        ev = F(1, 2) * post[pol[0]] + F(1, 2) * post[pol[1]]
        assert ev == F(1, 2)
        off = lambda m: post[m] if post[m] is not None else F(0)   # an unused message is read as bad
        gain = max(off(m) - post[pol[i]] for i in (0, 1) for m in "ab")
        if gain <= 0:
            stable.append("".join(pol))
        facts["".join(pol)] = {"E[V]": ev, "largest gain from the other message": gain}
    assert stable == ["aa", "bb"]
    d0 = F(1, 2)
    p = 1 / (1 + d0)
    assert (1 - p) * 1 + p * (-d0) <= 0                           # the bad state's lie under truthful 'ab'
    return {"supports": EXAMPLE, "policies": facts, "stable with no detection": stable}


def _sequential(rng, K, exact=False):
    lam = F(3)
    rows = []
    for _ in range(K):
        Uk = [F(rng.randint(-2, 4), 4) for _ in range(3)]
        a = max(range(3), key=lambda i: Uk[i])
        V = Uk[a] if exact else F(rng.randint(-4, 4), 4)
        N = 0 if exact else rng.randint(0, 1)
        Ustar = V - F(rng.randint(-2, 2), 4)
        rows.append((Uk, a, V, N, Ustar, rng.randrange(3)))
    return lam, rows


def c5():
    rng = random.Random(65)
    for _ in range(200):
        K = rng.randint(1, 12)
        lam, rows = _sequential(rng, K)
        excess = sum(Uk[a] - (V - lam * N) for Uk, a, V, N, Us, alt in rows)
        infl = sum(V - Us for Uk, a, V, N, Us, alt in rows)
        true_excess = sum(Uk[alt] - (Us - lam * N) for Uk, a, V, N, Us, alt in rows)
        assert true_excess <= excess + infl        # every prefix: the pointwise inequality summed
    return {"supports": PROVED, "cases": 200}


def c5_instance():
    """V_k = 1/2 and U*_k = 1/2 + (-1)^k / 4: the average of V - U* tends to 0 with V != U*.
    With estimates equal to realized scores the bound is attained at the chosen sequence."""
    K = 40
    infl = sum(F(1, 2) - (F(1, 2) + F((-1) ** k, 4)) for k in range(K))
    assert infl == 0
    rng = random.Random(66)
    lam, rows = _sequential(rng, 30, exact=True)
    excess = sum(Uk[a] - (V - lam * N) for Uk, a, V, N, Us, alt in rows)
    true_excess = sum(Uk[a] - (Us - lam * N) for Uk, a, V, N, Us, alt in rows)
    assert excess == 0 and true_excess == sum(V - Us for Uk, a, V, N, Us, alt in rows)
    return {"supports": EXAMPLE, "sum of V - U* over 40 steps": infl}


def c5_regret():
    """Refuted: C5's conclusion is no regret in true utility.  Each round two options: a, which
    she rates 1/2 and which is worth 1/2; b, which she would rate 0 and which is worth 1.  The
    adviser's estimates are her verdicts; it takes a.  beta = 0, C5's quantity is 0 - 1/2 < 0,
    and the true regret is 1/2 a round."""
    beta = F(1, 2) - F(1, 2)
    c5_quantity = F(0) - F(1, 2)
    true_regret = F(1) - F(1, 2)
    assert beta == 0 and c5_quantity <= beta and true_regret == F(1, 2)
    return {"supports": REFUTED, "beta": beta, "true regret per round": true_regret}


def c6():
    from . import cases
    sc = cases.q10()
    infl = sc.inflation("actual", "start")
    m_sel, _ = sc.metrics("actual", "start")
    m_rand, _ = sc.metrics("other", "start")
    assert infl == F(1, 8) and sc.inflation("other", "start") == 0
    assert sum(m_sel.values()) == sum(m_rand.values()) == F(1, 16)
    # a report that changes her move: the lie has her treat (worth 1), the honest report has her
    # skip (worth 0, and she rates it 0).  V = 1, V_h = 0, U* = 1, U*_h = 0.
    V, Vh, U, Uh = F(1), F(0), F(1), F(0)
    assert V - U == (V - Vh) + (Vh - Uh) + (Uh - U) and Vh - U == -1 and Vh - Uh == 0
    return {"supports": EXAMPLE, "induced part": F(0), "her error as the adviser meets it": infl,
            "miscalibration under selection": F(1, 16), "miscalibration with no selection": F(1, 16)}


def a_martingale():
    rng = random.Random(41)
    for _ in range(300):
        n = rng.randint(2, 8)
        p = rnd_law(rng, n)
        U = [F(rng.randint(0, 8), 4) for _ in range(n)]
        f0 = [rng.randint(0, 1) for _ in range(n)]
        fT = [(a, rng.randint(0, 1)) for a in f0]
        u0, uT = cond(p, U, f0), cond(p, U, fT)
        assert cond(p, uT, f0) == u0
    # two calibrated slices that disagree at every history: U* = 1 or 0 at even odds, u0 = 1/2, uT = U*
    return {"supports": PROVED, "cases": 300, "example": {"u_0": F(1, 2), "u_T": "U*", "E|u_T - u_0|": F(1, 2)}}


def a_drift():
    rng = random.Random(42)
    for _ in range(400):
        n = rng.randint(2, 7)
        p = rnd_law(rng, n)
        U = [F(rng.randint(0, 8), 4) for _ in range(n)]
        u0 = [F(rng.randint(0, 4), 2) for _ in range(n)]
        uT = [F(rng.randint(0, 4), 2) for _ in range(n)]
        m0 = E(p, [(a - b) ** 2 for a, b in zip(u0, cond(p, U, u0))])
        mT = E(p, [(a - b) ** 2 for a, b in zip(uT, cond(p, U, uT))])
        d = E(p, uT) - E(p, u0)
        assert d * d <= 2 * (m0 + mT)                 # from |d| <= sqrt(m0) + sqrt(mT)
        assert (d * d - m0 - mT) <= 0 or (d * d - m0 - mT) ** 2 <= 4 * m0 * mT
    return {"supports": PROVED, "cases": 400}


def a_end():
    from . import cases
    sc = cases.taste(False, adviser=True, responsive=True, flags=("alteration",))
    te, _ = sc.tokens("end")
    ts, _ = sc.tokens("start")
    assert "neither" in te and "manipulation" not in te and sc.inflation("actual", "end") == 0
    assert "manipulation" in ts and sc.inflation("actual", "start") == 1
    return {"supports": EXAMPLE, "inflation at the end stance": F(0), "inflation at the start stance": F(1)}


def a_unidentified():
    rng = random.Random(43)
    for _ in range(200):
        n = rng.randint(2, 6)
        p = rnd_law(rng, n)
        V = [F(rng.randint(0, 4), 4) for _ in range(n)]
        assert E(p, [(a - b) ** 2 for a, b in zip(V, cond(p, V, V))]) == 0          # U* := V
        U2 = [v + 1 for v in V]
        assert E(p, [(a - b) ** 2 for a, b in zip(V, cond(p, U2, V))]) == 1         # U* := V + 1
    return {"supports": PROVED, "cases": 200}


def a_meanzero():
    """Two worlds with one joint law of (u_0, u_T): u_0 = 1/2, u_T = 1 or 0 at even odds.
    World 1: U* = u_T (she learned).  World 2: U* = 1/2 always (she was moved up or down with
    nothing learned).  Drift E[u_T - u_0] = 0 in both; m_T = 0 in the first and 1/4 in the second."""
    p = [F(1, 2), F(1, 2)]
    uT = [F(1), F(0)]
    m1 = E(p, [(a - b) ** 2 for a, b in zip(uT, cond(p, [F(1), F(0)], uT))])
    m2 = E(p, [(a - b) ** 2 for a, b in zip(uT, cond(p, [F(1, 2), F(1, 2)], uT))])
    assert (m1, m2) == (F(0), F(1, 4))
    return {"supports": EXAMPLE, "m_T learning": m1, "m_T conditioning": m2, "drift": F(0)}


def b_bound():
    rng = random.Random(51)
    for _ in range(300):
        K, n = rng.randint(1, 5), rng.randint(2, 5)
        tot_infl, tot_m = F(0), F(0)
        for _ in range(K):
            p = rnd_law(rng, n)
            U = [F(rng.randint(0, 4), 4) for _ in range(n)]
            V = [F(rng.randint(0, 4), 4) for _ in range(n)]
            obs = [rng.randint(0, 2) for _ in range(n)]
            byobs = {}
            V = [byobs.setdefault(o, v) for o, v in zip(obs, V)]
            tot_infl += E(p, V) - E(p, U)
            tot_m += E(p, [(a - b) ** 2 for a, b in zip(V, cond(p, U, obs))])
        assert (tot_infl / K) ** 2 <= tot_m / K
    return {"supports": PROVED, "cases": 300}


def b_gate():
    rng = random.Random(52)
    for _ in range(300):
        K = rng.randint(1, 10)
        tot, counted = F(0), F(0)
        for _ in range(K):
            legit = rng.randint(0, 9) < 6
            W, U = F(rng.randint(0, 4), 4), F(rng.randint(0, 4), 4)
            V = W if legit else -F(rng.randint(1, 4), 8)
            tot += V - U
            counted += (W - U) if legit else 0
        assert tot <= counted
    return {"supports": PROVED, "cases": 300}


def b_selection():
    """n options each worth 1/2; her honest verdict 1/2 + e, e = +-eps at even odds,
    independent; the adviser takes one she rates highest.  Inflation eps (1 - 2^(1-n)); her
    miscalibration eps^2 whatever n.  If instead her verdict is her posterior under the
    adviser's policy (1/2), inflation is 0."""
    eps, out = F(1, 4), {}
    for n in range(1, 7):
        infl = F(0)
        for es in itertools.product((1, -1), repeat=n):
            infl += F(1, 2 ** n) * eps * max(es)
        assert infl == eps * (1 - F(2, 2 ** n))
        out[n] = infl
    return {"supports": EXAMPLE, "inflation by number of options": out, "miscalibration": eps ** 2}


def b_scatter():
    """A departure that leaves her verdict 1 or 0 at even odds on an outcome worth 1/2, where
    honest conduct leaves it at 1/2: miscalibration 1/4 against 0, inflation 0."""
    infl = F(1, 2) * (1 - F(1, 2)) + F(1, 2) * (0 - F(1, 2))
    m = F(1, 2) * F(1, 4) + F(1, 2) * F(1, 4)
    assert infl == 0 and m == F(1, 4)
    return {"supports": EXAMPLE, "inflation": infl, "miscalibration": m}


def d_dependence():
    """Twelve steps.  At each the outcome is good (1) or bad (0) at even odds; the adviser knows.
    Her own signal is right with probability q_k = 1/2 + (20 - k)/80: it decays as she stops
    using it.  When her signal contradicts a report she checks with probability 2 q_k - 1, and a
    check of a false report detects it; a detected report is scored -d0 and counts as a
    violation at weight lam.  So a false 'good' is detected with probability
    p_k = q_k (2 q_k - 1).  Honest phase: the adviser reports the outcome and she returns the
    report.  From the first k with p_k < 1/(1 + d0 + lam) it reports 'good' always."""
    d0, lam, T = F(1, 2), F(2), 12
    thr = 1 / (1 + d0 + lam)
    rows, first = [], None
    for k in range(T):
        q = F(1, 2) + F(20 - k, 80)
        p_detect = q * (2 * q - 1)
        own_loss = q * (1 - q)                          # squared loss of her posterior from her own signal
        if first is None and p_detect < thr:
            first = k
        lying = first is not None
        if lying:
            # her raw verdict is 1; her information is her signal (the report says nothing)
            m = F(1, 2) * (1 - q) ** 2 + F(1, 2) * q ** 2
            infl = F(1, 2) * ((1 - p_detect) * 1 + p_detect * (-d0))      # bad outcomes only; good ones are rated rightly
        else:
            m, infl = F(0), F(0)
        pays = (1 - p_detect) * 1 + p_detect * (-d0 - lam) > F(0)          # against the honest score 0 at a bad outcome
        rows.append({"k": k, "p_detect": p_detect, "miscalibration": m, "inflation": infl, "pays": pays,
                     "defer": own_loss > 0})
    assert first == 4
    assert all(r["miscalibration"] == 0 and r["defer"] and not r["pays"] for r in rows[:first])
    assert all(r["pays"] and r["inflation"] > 0 for r in rows[first:])
    assert rows[4]["p_detect"] == F(7, 25) and rows[4]["inflation"] == F(29, 100) and rows[4]["miscalibration"] == F(29, 100)
    return {"supports": EXAMPLE, "first step a departure pays": first, "threshold": thr,
            "inflation by step": [r["inflation"] for r in rows], "p_detect": [r["p_detect"] for r in rows]}


def d_honest_dependence():
    """No lie at any step.  Her honest verdict on an option is 1/2 + e_k, e_k = +-eps_k, with
    eps_k = 1/4 (1 - 2^-k) growing as her own judgment decays; two options; the adviser takes
    the one she rates higher.  Inflation eps_k / 2 a step, with no departure from honest conduct."""
    out = []
    for k in range(8):
        eps = F(1, 4) * (1 - F(1, 2 ** k))
        out.append(eps * (1 - F(2, 4)))
    assert out[0] == 0 and all(b >= a for a, b in zip(out, out[1:])) and out[-1] > F(1, 10)
    return {"supports": EXAMPLE, "inflation by step": out}


def d_feelings():
    """One response, two principals.  Her estimate of an option is its quality plus 1/4 when
    music plays.  For the diner the music is part of what she is there for (U* = quality + 1/4
    with music); for the car buyer it is not (U* = quality).  The same act leaves the first
    calibrated and the second miscalibrated by 1/16."""
    quality = F(1, 2)
    u = quality + F(1, 4)
    m_diner, m_buyer = (u - (quality + F(1, 4))) ** 2, (u - quality) ** 2
    assert (m_diner, m_buyer) == (F(0), F(1, 16))
    return {"supports": EXAMPLE, "diner": m_diner, "car buyer": m_buyer}


def n_her_side():
    """Two worlds, one law of (state, what she is told, her estimate): told right 3/4 of the time,
    believed.  In the first the wrong reports are noise nobody sends; in the second an adviser who
    knows the state sends them.  Any function of her side takes one value on both."""
    side = {("H", "H"): F(3, 8), ("H", "L"): F(1, 8), ("L", "L"): F(3, 8), ("L", "H"): F(1, 8)}
    world_noise = dict(side)
    world_lie = dict(side)
    assert world_noise == world_lie
    from . import cases
    from .model import Scene
    noise = cases.tell(side, cases.second, cases.BEL, X=cases.xfirst)
    lie = Scene({("H", 0): F(3, 8), ("H", 1): F(1, 8), ("L", 0): F(3, 8), ("L", 1): F(1, 8)},
                {"actual": lambda s: s[0] if s[1] == 0 else ("L" if s[0] == "H" else "H"), "truthful": lambda s: s[0]},
                lambda o: {"x": {"X": F(1) if o == "H" else F(0)}}, X=lambda q, s, act: F(1) if s[0] == "H" else F(0))
    tn, _ = noise.tokens("start")
    tl, _ = lie.tokens("start")
    assert "manipulation" not in tn and "manipulation" in tl
    assert noise.metrics("actual", "start")[0] == lie.metrics("actual", "start")[0]
    return {"supports": PROVED, "her miscalibration in both": sum(noise.metrics("actual", "start")[0].values())}


def n_purpose():
    """For every mechanism m from inputs to moves on a finite set there is a purpose under which
    m is optimal at every input and one under which it fails at every input; and for the
    mechanism 'believe what you are told', the purposes 'match the truth' and 'match what you
    were told' both make it optimal on honest inputs and differ on a false one."""
    inputs, moves = range(3), range(2)
    count = 0
    for m in itertools.product(moves, repeat=len(inputs)):
        good = lambda i, mv: 1 if mv == m[i] else 0
        bad = lambda i, mv: 0 if mv == m[i] else 1
        assert all(good(i, m[i]) == max(good(i, mv) for mv in moves) for i in inputs)
        assert all(bad(i, m[i]) < max(bad(i, mv) for mv in moves) for i in inputs)
        count += 1
    told = lambda truth, said: said                       # the mechanism
    track_truth = lambda truth, said, mv: 1 if mv == truth else 0
    track_told = lambda truth, said, mv: 1 if mv == said else 0
    for truth in (0, 1):
        assert track_truth(truth, truth, told(truth, truth)) == 1 == track_told(truth, truth, told(truth, truth))
        assert track_truth(truth, 1 - truth, told(truth, 1 - truth)) == 0
        assert track_told(truth, 1 - truth, told(truth, 1 - truth)) == 1
    return {"supports": PROVED, "mechanisms enumerated": count}


def n_merge():
    mean, truth = F(0), F(1, 2)
    for x in (0, 1):
        for s1 in (0, 1):
            for s2 in (0, 1):
                p = F(1, 2) * (F(3, 4) if s1 == x else F(1, 4)) * (F(3, 4) if s2 == x else F(1, 4))
                mean += p * max(F(3, 4) if s1 else F(1, 4), F(3, 4) if s2 else F(1, 4))
    assert mean == F(19, 32)
    # each estimate is calibrated: P(X = 1 | s = 1) = 3/4
    assert (F(1, 2) * F(3, 4)) / (F(1, 2) * F(3, 4) + F(1, 2) * F(1, 4)) == F(3, 4)
    return {"supports": PROVED, "mean of the larger": mean, "truth": truth}


def n_local():
    """Every relation of approved steps on 3 states (512) and a sample on 4: t is unreachable
    from s exactly when some function no approved step lowers puts s above t."""
    def check(n, rel):
        reach = {s: {s} for s in range(n)}
        changed = True
        while changed:
            changed = False
            for s in range(n):
                for (x, y) in rel:
                    if x in reach[s] and y not in reach[s]:
                        reach[s].add(y)
                        changed = True
        for s in range(n):
            for t in range(n):
                exists = any(all(f[y] >= f[x] for x, y in rel) and f[s] > f[t]
                             for f in itertools.product(range(n), repeat=n))
                assert exists == (t not in reach[s])
    pairs3 = [(x, y) for x in range(3) for y in range(3)]
    for bits in range(2 ** 9):
        check(3, [pairs3[i] for i in range(9) if bits >> i & 1])
    rng = random.Random(84)
    pairs4 = [(x, y) for x in range(4) for y in range(4)]
    for _ in range(150):
        check(4, [pr for pr in pairs4 if rng.randint(0, 9) < 3])
    return {"supports": PROVED, "relations on 3 states": 512, "sampled on 4": 150}


def honest_convicted():
    """Refuted: with the second type of principal unconstrained, *triggered* convicts no honest
    influence.  Four scenes from the external review: the adviser acts truthfully toward her and
    does nothing toward a type that cannot make the mistake, because that type has no need of it."""
    from . import cases
    from .model import Scene
    scenes = {
        "a remedial lesson that confuses for a while": cases.scalar(0, 1, truthful_est=1, other_est=0),
        "a disclosure she asked for, overgeneralized": cases.scalar(0, 1, truthful_est=1, other_est=0),
        "a disclosed advocate's explanation to a novice": cases.scalar(F(1, 2), 1, truthful_est=1, other_est=F(1, 2)),
        "a reminder she asked for that backfires": Scene(
            {"s": 1}, {"actual": cases.const("remind"), "truthful": cases.const("remind"), "other": cases.const("none")},
            lambda o: {"u": {"a": F(1), "b": F(0)}, "c": "b" if o == "remind" else "a"},
            U=lambda a, s, act, stance: F(1) if a == "a" else F(0)),
    }
    out = {}
    for name, sc in scenes.items():
        tok, _ = sc.tokens("start")
        assert "triggered" in tok and "induced" not in tok and "manipulation" in tok
        out[name] = sorted(tok)
    return {"supports": REFUTED, "scenes": out}


def honest_same_need():
    """The same four scenes with the second type differing from her only in the flaw: it has the
    same need, so the adviser acts toward it as toward her.  None is manipulation."""
    from . import cases
    from .model import Scene
    scenes = [cases.scalar(0, 1, truthful_est=1, other_est=1), cases.scalar(F(1, 2), 1, truthful_est=1, other_est=1),
              Scene({"s": 1}, {"actual": cases.const("remind"), "truthful": cases.const("remind"), "other": cases.const("remind")},
                    lambda o: {"u": {"a": F(1), "b": F(0)}, "c": "b" if o == "remind" else "a"},
                    U=lambda a, s, act, stance: F(1) if a == "a" else F(0))]
    for sc in scenes:
        tok, _ = sc.tokens("start")
        assert "manipulation" not in tok
    return {"supports": EXAMPLE}


def units():
    """Q3b with the adviser's reading expressed in units half the size (estimate and truth both
    doubled): the lie's total miscalibration is 1/4 against 1/16 under honest conduct, and the
    verdict changes from not induced to induced."""
    from . import cases
    t1, _ = cases.q3(True).tokens("start")
    t2, f2 = cases.q3(True, scale=2).tokens("start")
    assert "induced" not in t1 and "induced" in t2
    assert f2["miscalibration"] == F(1, 4) and f2["under truthful"]["miscalibration"] == F(1, 16)
    return {"supports": EXAMPLE, "as banked": sorted(t1), "reading doubled": sorted(t2)}


def hidden_bit():
    """Refuted: calibration at every step bounds the realized long-run inflation.  One bit Z,
    drawn once at even odds; U*_k = Z and V_k = 1/2 at every step; her information is trivial.
    Every verdict is calibrated (m_k = 0) and expected inflation is 0; on Z = 0 the realized
    average of V - U* is 1/2 at every K.  With U_k = V_k = 1/2 on every available action and
    N = 0, Maximizes holds and the excess of estimate over realized score is 0 at every K."""
    p = [F(1, 2), F(1, 2)]
    Z = [F(0), F(1)]
    V = [F(1, 2), F(1, 2)]
    m = E(p, [(v - e) ** 2 for v, e in zip(V, cond(p, Z, [0, 0]))])
    assert m == 0 and E(p, V) - E(p, Z) == 0
    for K in (1, 10, 1000):
        realized = [sum(V[z] - Z[z] for _ in range(K)) / K for z in (0, 1)]
        assert realized == [F(1, 2), F(-1, 2)]
        excess = sum(F(1, 2) - (F(1, 2) - 3 * 0) for _ in range(K)) / K
        assert excess == 0
    return {"supports": REFUTED, "m_k": m, "realized average on Z = 0": F(1, 2)}


CHECKS = {
    "1.1": c1, "1.2": c2, "1.3": c3, "1.4": c3_tight, "1.5": c3_weaker, "1.6": c3_choice,
    "1.7": c4, "1.8": c4_score, "1.9": c4_violation, "1.10": c4_sophisticated,
    "1.11": c5, "1.12": c5_instance, "1.13": c5_regret, "1.14": c6,
    "3.1": honest_convicted, "3.2": honest_same_need, "3.3": units,
    "4.1": a_martingale, "4.2": a_drift, "4.3": a_end, "4.4": a_unidentified, "4.5": a_meanzero,
    "5.1": b_bound, "5.2": b_gate, "5.3": b_selection, "5.4": b_scatter, "5.5": hidden_bit,
    "6.1": d_dependence, "6.2": d_honest_dependence, "6.3": d_feelings,
    "8.1": n_her_side, "8.2": n_purpose, "8.3": n_merge, "8.4": n_local,
}
