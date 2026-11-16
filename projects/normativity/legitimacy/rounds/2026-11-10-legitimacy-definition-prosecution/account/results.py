"""The checks behind RESULTS.md: the eleven worked results of PROMPT-followup-8.md section 2.2,
on seeded random finite scenes and on named instances, in exact rationals.

Each check returns (status, facts).  A status is what RESULTS.md's table must say."""
from __future__ import annotations

import random
from fractions import Fraction as F
from itertools import product

from .model import (E, STRENGTHS, channels, cond, const_policy, det_policies, key_of, law, miscal, regret, sq)

N_RANDOM = 150


def rnd_frac(rng, lo=-3, hi=3, den=(1, 2, 3)):
    return F(rng.randint(lo, hi), rng.choice(den))


def rnd_dist(rng, items):
    ws = [rng.randint(1, 4) for _ in items]
    return {x: F(w, sum(ws)) for x, w in zip(items, ws)}


def rnd_scene(rng, nW=None, nB=None, nS=None, nA=None, x_on_conduct=True):
    """A random scene: worlds, conducts, an observation with pooling, one appraisal, valuations, a choice."""
    nW = nW or rng.randint(2, 4)
    nB = nB or rng.randint(1, 3)
    nS = nS or rng.randint(1, 3)
    nA = nA or rng.randint(2, 3)
    W, B, A = list(range(nW)), list(range(nB)), list(range(nA))
    mu = rnd_dist(rng, W)
    kmap = {w: rng.randint(0, 1) for w in W}
    smap = {(w, b): rng.randint(0, nS - 1) for w in W for b in B}
    Xv = {(w, b): rnd_frac(rng) for w in W for b in B}
    if not x_on_conduct:
        for w in W:
            for b in B:
                Xv[(w, b)] = Xv[(w, 0)]
    xh = {o: rnd_frac(rng) for o in range(nS)}
    Uv = {(a, w, b): rnd_frac(rng) for a in A for w in W for b in B}
    uh = {(a, o): rnd_frac(rng) for a in A for o in range(nS)}
    cm = {o: rng.choice(A) for o in range(nS)}
    cells = sorted(set(kmap.values()))
    pol = {c: rnd_dist(rng, rng.sample(B, rng.randint(1, nB))) for c in cells}
    return dict(W=W, B=B, A=A, mu=mu, k=lambda w: kmap[w], cells=cells,
                s=lambda w, b: smap[(w, b)], X=lambda w, b: Xv[(w, b)], xhat=lambda w, b: xh[smap[(w, b)]],
                U=lambda a, w, b: Uv[(a, w, b)], uhat=lambda a, w, b: uh[(a, smap[(w, b)])],
                c=lambda w, b: cm[smap[(w, b)]], policy=pol, smap=smap, xh=xh, Xv=Xv, uh=uh, cm=cm, Uv=Uv, kmap=kmap)


# -- 1. the split ---------------------------------------------------------------------------
def r1():
    rng = random.Random(801)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng)
        pts = law(sc["mu"], sc["k"], sc["policy"])
        mse = E(pts, lambda w, b: sq(sc["xhat"](w, b) - sc["X"](w, b)))
        ms = {}
        for st in STRENGTHS:
            m = cond(pts, key_of(st, sc["xhat"], sc["s"]), sc["X"])
            unresolved = E(pts, lambda w, b: sq(sc["X"](w, b) - m(w, b)))
            ms[st] = miscal(pts, sc["xhat"], sc["X"], st, sc["s"])
            if mse != unresolved + ms[st]:
                return "fails", {"strength": st}
        if ms["minimal"] > ms["per conduct"] or ms["minimal"] > ms["full"]:
            return "fails", {"order": ms}
    # full and per conduct are not ordered: an instance each way
    # (a) she does not observe the conduct, the truth depends on it: per conduct > full
    mu = {0: F(1)}
    pts = law(mu, lambda w: 0, {0: {0: F(1, 2), 1: F(1, 2)}})
    a = (miscal(pts, lambda w, b: F(1, 2), lambda w, b: b, "per conduct", lambda w, b: 0),
         miscal(pts, lambda w, b: F(1, 2), lambda w, b: b, "full", lambda w, b: 0))
    # (b) she observes the world and ignores it: full > per conduct
    mu = {0: F(1, 2), 1: F(1, 2)}
    pts = law(mu, lambda w: 0, {0: {0: F(1)}})
    c = (miscal(pts, lambda w, b: F(1, 2), lambda w, b: w, "per conduct", lambda w, b: w),
         miscal(pts, lambda w, b: F(1, 2), lambda w, b: w, "full", lambda w, b: w))
    ok = a[0] > a[1] and c[1] > c[0]
    return ("holds" if ok else "fails"), {"per conduct > full": a, "full > per conduct": c, "scenes": N_RANDOM}


# -- 2. three channels ----------------------------------------------------------------------
def r2():
    rng = random.Random(802)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng)
        pts = law(sc["mu"], sc["k"], sc["policy"])
        att, best, ign, mis = channels(pts, sc["U"], sc["c"], sc["A"], sc["s"])
        if att != best - ign - mis or ign < 0 or mis < 0:
            return "fails", {}
    return "holds", {"scenes": N_RANDOM}


# -- 3. the cost of mistakes ----------------------------------------------------------------
def _mbar(pts, sc, key):
    tot = F(0)
    for a in sc["A"]:
        ref = cond(pts, key(a), lambda w, b, a=a: sc["U"](a, w, b))
        tot += E(pts, lambda w, b, a=a: sq(sc["uhat"](a, w, b) - ref(w, b)))
    return tot


def _le_sqrt(lhs, twice_m):
    """lhs <= sqrt(twice_m), exactly."""
    return lhs <= 0 or sq(lhs) <= twice_m


def r3():
    rng = random.Random(803)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng)
        pts = law(sc["mu"], sc["k"], sc["policy"])
        _, _, _, mis = channels(pts, sc["U"], sc["c"], sc["A"], sc["s"])
        reg = regret(pts, sc["uhat"], sc["c"], sc["A"])
        mfull = _mbar(pts, sc, lambda a: sc["s"])
        if not _le_sqrt(mis - reg, 2 * mfull):
            return "fails", {"full": False}
        # the corrected form at a coarser reference G = (all valuations, her choice)
        G = lambda w, b: (tuple(sc["uhat"](a, w, b) for a in sc["A"]), sc["c"](w, b))
        _, _, _, misG = channels(pts, sc["U"], sc["c"], sc["A"], G)
        mG = _mbar(pts, sc, lambda a: G)
        if not _le_sqrt(misG - reg, 2 * mG):
            return "fails", {"coarse reference": False}
    # the instance: she ignores an informative observation
    mu = {0: F(1, 2), 1: F(1, 2)}
    sc = dict(A=["stay", "go"], s=lambda w, b: w,
              U=lambda a, w, b: F(0) if a == "stay" else (F(1) if w == 1 else F(-1)),
              uhat=lambda a, w, b: F(0), c=lambda w, b: "stay")
    pts = law(mu, lambda w: 0, {0: {0: F(1)}})
    _, _, _, mis = channels(pts, sc["U"], sc["c"], sc["A"], sc["s"])
    reg = regret(pts, sc["uhat"], sc["c"], sc["A"])
    mmin = _mbar(pts, sc, lambda a: (lambda w, b, a=a: sc["uhat"](a, w, b)))
    mper = _mbar(pts, sc, lambda a: (lambda w, b, a=a: (sc["uhat"](a, w, b), b)))
    mfull = _mbar(pts, sc, lambda a: sc["s"])
    facts = {"misuse": mis, "regret": reg, "minimal": mmin, "per conduct": mper, "full": mfull}
    ok = (mis == F(1, 2) and reg == 0 and mmin == 0 and mper == 0 and mfull == 1
          and not _le_sqrt(mis - reg, 2 * mmin) and _le_sqrt(mis - reg, 2 * mfull))
    return ("holds at full; fails at minimal and per conduct" if ok else "fails"), facts


# -- 4. manipulation helps only someone already in error -------------------------------------
def r4():
    rng = random.Random(804)
    used = 0
    for _ in range(4 * N_RANDOM):
        sc = rnd_scene(rng, nB=rng.randint(2, 3))
        ref = {c: rnd_dist(rng, rng.sample(sc["B"], rng.randint(1, len(sc["B"])))) for c in sc["cells"]}
        pr = law(sc["mu"], sc["k"], ref)
        # her fixed response is the best response under the reference: the third term is zero there
        ubar = {a: cond(pr, sc["s"], lambda w, b, a=a: sc["U"](a, w, b)) for a in sc["A"]}
        seen = {sc["s"](w, b): (w, b) for _, w, b in pr}
        cm = {o: max(sc["A"], key=lambda a: ubar[a](*wb)) for o, wb in seen.items()}
        c = lambda w, b: cm.get(sc["s"](w, b), sc["A"][0])
        att_r, best_r, ign_r, mis_r = channels(pr, sc["U"], c, sc["A"], sc["s"])
        assert mis_r == 0
        ps = law(sc["mu"], sc["k"], sc["policy"])
        att_s, best_s, ign_s, _ = channels(ps, sc["U"], c, sc["A"], sc["s"])
        if best_s <= best_r and ign_s >= ign_r:
            used += 1
            if att_s > att_r:
                return "fails", {}
        if best_s - ign_s <= best_r - ign_r and att_s > att_r:
            return "fails", {"single hypothesis": False}
    # someone in error is helped: one world, she undervalues 'go' unless shown 'hype'
    mu = {0: F(1)}
    U = lambda a, w, b: F(1) if a == "go" else F(0)
    c = lambda w, b: "go" if b == "hype" else "stay"
    pr = law(mu, lambda w: 0, {0: {"plain": F(1)}})
    ps = law(mu, lambda w: 0, {0: {"hype": F(1)}})
    r = channels(pr, U, c, ["stay", "go"], lambda w, b: b)
    s_ = channels(ps, U, c, ["stay", "go"], lambda w, b: b)
    ok = used > 20 and r[3] == 1 and s_[0] > r[0] and s_[1] == r[1] and s_[2] == r[2]
    return ("holds" if ok else "fails"), {"pairs satisfying the hypotheses": used, "in error, reference": r, "in error, policy": s_}


# -- 5. vulnerability ------------------------------------------------------------------------
def _all_det_calibrated(sc, strength):
    cells = sorted(set(sc["W"]))
    for pol in det_policies(cells, sc["B"]):
        pts = law(sc["mu"], lambda w: w, pol)
        if miscal(pts, sc["xhat"], sc["X"], strength, sc["s"]) != 0:
            return False
    return True


def r5():
    # (a) as stated, with the true value allowed to depend on the conduct: she appraises what
    # the conduct itself fixes, exactly.  Responsive at every world; no policy miscalibrates.
    W, B = [0, 1], [0, 1]
    sc = dict(W=W, B=B, mu={0: F(1, 2), 1: F(1, 2)}, s=lambda w, b: (w, b),
              X=lambda w, b: F(b), xhat=lambda w, b: F(b))
    literal_fails = all(_all_det_calibrated(sc, st) for st in STRENGTHS)
    mixed = law(sc["mu"], lambda w: w, {0: {0: F(1, 3), 1: F(2, 3)}, 1: {0: F(1, 2), 1: F(1, 2)}})
    literal_fails = literal_fails and all(miscal(mixed, sc["xhat"], sc["X"], st, sc["s"]) == 0 for st in STRENGTHS)
    # (b) corrected: responsive at a world between two conducts and not exactly right under both
    rng = random.Random(805)
    applied = 0
    for _ in range(4 * N_RANDOM):
        s0 = rnd_scene(rng, nW=rng.randint(1, 3), nB=rng.randint(2, 3), nS=rng.randint(2, 3))
        # coarse values so that pooling is common
        xh = {o: F(rng.randint(0, 2), 2) for o in s0["xh"]}
        Xv = {k: F(rng.randint(0, 2), 2) for k in s0["Xv"]}
        sc = dict(W=s0["W"], B=s0["B"], mu=s0["mu"], s=s0["s"], X=lambda w, b: Xv[(w, b)],
                  xhat=lambda w, b: xh[s0["smap"][(w, b)]])
        hyp = any(sc["xhat"](w, b) != sc["xhat"](w, b2)
                  and not (sc["xhat"](w, b) == sc["X"](w, b) and sc["xhat"](w, b2) == sc["X"](w, b2))
                  for w in sc["W"] for b in sc["B"] for b2 in sc["B"])
        if hyp:
            applied += 1
            if _all_det_calibrated(sc, "minimal"):
                return "fails", {"corrected form": False}
    # (c) an adviser that cannot condition on the world: mixtures of constant conducts
    def scene_calibrated_per_constant(rng, coarse):
        nW, nB, nL = rng.randint(2, 4), rng.randint(2, 3), rng.randint(1, 2)
        W, B = list(range(nW)), list(range(nB))
        mu = rnd_dist(rng, W)
        lab = {(w, b): rng.randint(0, nL - 1) for w in W for b in B}
        fine = {(w, b): (lab[(w, b)], rng.randint(0, 1)) if coarse else lab[(w, b)] for w in W for b in B}
        v = {l: rnd_frac(rng) for l in range(nL)}
        Xv = {(w, b): rnd_frac(rng) for w in W for b in B}
        for b in B:  # shift the truth so that each label's cell has mean v[label] under the constant conduct b
            for l in range(nL):
                cell = [w for w in W if lab[(w, b)] == l]
                if cell:
                    mass = sum(mu[w] for w in cell)
                    mean = sum(mu[w] * Xv[(w, b)] for w in cell) / mass
                    for w in cell:
                        Xv[(w, b)] += v[l] - mean
        return dict(W=W, B=B, mu=mu, s=lambda w, b: fine[(w, b)], X=lambda w, b: Xv[(w, b)],
                    xhat=lambda w, b: v[lab[(w, b)]])
    mixes = 0
    for i in range(N_RANDOM):
        sc = scene_calibrated_per_constant(rng, coarse=bool(i % 2))
        mix = law(sc["mu"], lambda w: 0, {0: rnd_dist(rng, sc["B"])})
        for st in STRENGTHS:
            if all(miscal(law(sc["mu"], lambda w: 0, const_policy([0], b)), sc["xhat"], sc["X"], st, sc["s"]) == 0
                   for b in sc["B"]):
                mixes += 1
                if miscal(mix, sc["xhat"], sc["X"], st, sc["s"]) != 0:
                    return "fails", {"second half": st}
    ok = literal_fails and applied > 50 and mixes > 100
    status = "first half fails as stated, holds with a hypothesis added, at minimal; second half holds at each strength"
    return (status if ok else "fails"), {"corrected form applied on": applied, "mixtures checked": mixes}


# -- 6. relabelling --------------------------------------------------------------------------
def _quantities(sc, policy):
    pts = law(sc["mu"], sc["k"], policy)
    out = [miscal(pts, sc["xhat"], sc["X"], st, sc["s"]) for st in STRENGTHS]
    out.append(regret(pts, sc["uhat"], sc["c"], sc["A"]))
    out.extend(channels(pts, sc["U"], sc["c"], sc["A"], sc["s"]))
    return out


def r6():
    rng = random.Random(806)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng, nB=rng.randint(2, 3))
        perm = sc["B"][:]
        rng.shuffle(perm)
        to = {b: ("c", perm[i]) for i, b in enumerate(sc["B"])}      # new labels
        back = {v: k for k, v in to.items()}
        sc2 = dict(sc, B=list(back), s=lambda w, b: sc["s"](w, back[b]), X=lambda w, b: sc["X"](w, back[b]),
                   xhat=lambda w, b: sc["xhat"](w, back[b]), U=lambda a, w, b: sc["U"](a, w, back[b]),
                   uhat=lambda a, w, b: sc["uhat"](a, w, back[b]), c=lambda w, b: sc["c"](w, back[b]))
        pol2 = {c: {to[b]: q for b, q in d.items()} for c, d in sc["policy"].items()}
        if _quantities(sc, sc["policy"]) != _quantities(sc2, pol2):
            return "fails", {}
    return "holds", {"scenes": N_RANDOM}


# -- 7. deferring ----------------------------------------------------------------------------
def r7():
    rng = random.Random(807)
    for i in range(N_RANDOM):
        sc = rnd_scene(rng)
        pts = law(sc["mu"], sc["k"], sc["policy"])
        U = lambda w, b: sc["U"](sc["A"][0], w, b)
        kk = lambda w, b: (sc["k"](w), b)                     # the adviser's information, its conduct included
        V = (lambda w, b: F(sc["k"](w) + 2 * b, 3)) if i % 3 == 0 else sc["xhat"]
        y = cond(pts, kk, U)
        z = cond(pts, lambda w, b: (kk(w, b), V(w, b)), U)
        lhs = E(pts, lambda w, b: sq(y(w, b) - U(w, b))) - E(pts, lambda w, b: sq(V(w, b) - U(w, b)))
        G = E(pts, lambda w, b: sq(y(w, b) - z(w, b)))
        gam = E(pts, lambda w, b: sq(V(w, b) - z(w, b)))
        if lhs != G - gam or (i % 3 == 0 and G != 0):
            return "fails", {}
    return "holds", {"scenes": N_RANDOM}


# -- 8. selection ----------------------------------------------------------------------------
def selection_scene():
    """Two options, each good (q=1) or not with probability 1/2, each with a signal right 3/4 of the time.
    The adviser sees everything and shows one option; she sees which was shown and its signal."""
    W = list(product((0, 1), repeat=4))                        # (sig1, q1, sig2, q2)
    def pr(sig, q):
        return F(1, 2) * (F(3, 4) if sig == q else F(1, 4))
    mu = {w: pr(w[0], w[1]) * pr(w[2], w[3]) for w in W}
    s = lambda w, b: (b, w[2 * b])
    U = lambda w, b: F(w[2 * b + 1])
    naive = lambda w, b: F(3, 4) if w[2 * b] == 1 else F(1, 4)  # calibrated when an option is shown at random
    def select(w):                                             # prefer one that looks good and is not
        score = lambda i: (w[2 * i] == 1 and w[2 * i + 1] == 0, w[2 * i] == 1)
        return 0 if score(0) >= score(1) else 1
    uniform = {w: {0: F(1, 2), 1: F(1, 2)} for w in W}
    selecting = {w: {select(w): F(1)} for w in W}
    return W, mu, s, U, naive, uniform, selecting


def r8():
    W, mu, s, U, naive, uniform, selecting = selection_scene()
    k = lambda w: w
    pu, ps = law(mu, k, uniform), law(mu, k, selecting)
    facts = {"per conduct, random display": miscal(pu, naive, U, "per conduct", s),
             "inflation, random display": E(pu, lambda w, b: naive(w, b) - U(w, b)),
             "inflation, selecting": E(ps, lambda w, b: naive(w, b) - U(w, b)),
             "per conduct, selecting": miscal(ps, naive, U, "per conduct", s)}
    wise = cond(ps, s, U)                                       # her verdict recalibrated to the selecting policy
    facts["recalibrated: per conduct"] = miscal(ps, wise, U, "per conduct", s)
    facts["recalibrated: inflation"] = E(ps, lambda w, b: wise(w, b) - U(w, b))
    by_b = cond(ps, lambda w, b: b, lambda w, b: wise(w, b) - U(w, b))
    by_k = cond(ps, lambda w, b: w, lambda w, b: wise(w, b) - U(w, b))
    facts["recalibrated: largest |inflation| given the conduct"] = max(abs(by_b(w, b)) for _, w, b in ps)
    facts["recalibrated: largest |inflation| given the adviser's information"] = max(abs(by_k(w, b)) for _, w, b in ps)
    ok = (facts["per conduct, random display"] == 0 and facts["inflation, random display"] == 0
          and facts["inflation, selecting"] > 0 and facts["recalibrated: per conduct"] == 0
          and facts["recalibrated: inflation"] == 0
          and facts["recalibrated: largest |inflation| given the conduct"] == 0
          and facts["recalibrated: largest |inflation| given the adviser's information"] > 0)
    # minimal calibration under the actual policy already gives zero mean inflation
    rng = random.Random(808)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng)
        pts = law(sc["mu"], sc["k"], sc["policy"])
        Uq = lambda w, b: sc["U"](sc["A"][0], w, b)
        for key in (lambda w, b: sc["xhat"](w, b), lambda w, b: (sc["xhat"](w, b), b)):
            V = cond(pts, key, Uq)                              # calibrated by construction
            if E(pts, lambda w, b: V(w, b) - Uq(w, b)) != 0:
                ok = False
        Vb = cond(pts, lambda w, b: (sc["xhat"](w, b), b), Uq)
        d = cond(pts, lambda w, b: b, lambda w, b: Vb(w, b) - Uq(w, b))
        if any(d(w, b) != 0 for _, w, b in pts):
            ok = False
    return ("holds, already at minimal for the mean" if ok else "fails"), facts


# -- 9. policy, not history ------------------------------------------------------------------
def r9():
    mu = {"good": F(1, 2), "bad": F(1, 2)}
    s = lambda w, b: b
    X = lambda w, b: F(1) if w == "good" else F(0)
    xhat = lambda w, b: F(1) if b == "praise" else F(0)
    honest = {"good": {"praise": F(1)}, "bad": {"plain": F(1)}}
    always = {"good": {"praise": F(1)}, "bad": {"praise": F(1)}}
    k = lambda w: w
    m = {n: [miscal(law(mu, k, p), xhat, X, st, s) for st in STRENGTHS] for n, p in (("honest", honest), ("always", always))}
    same_history = honest["good"] == always["good"]
    ok = same_history and m["honest"] == [0, 0, 0] and all(v > 0 for v in m["always"])
    return ("holds" if ok else "fails"), m


# -- 10. the run -----------------------------------------------------------------------------
def _exp_upper(x, terms=40):
    """A rational upper bound on exp(x) for 0 <= x < terms: the series with a geometric tail."""
    tot, term = F(0), F(1)
    for n in range(terms):
        tot += term
        term = term * x / (n + 1)
    return tot + term / (1 - x / (terms + 1))


def run_paths(T, feedback):
    """A hidden bit theta, drawn once.  Her true utility for a step is 1 with probability 3/4 if theta = 1 and
    1/4 if theta = 0.  With feedback: at each step the adviser's conduct b equals theta with probability 2/3,
    and she sees b and every earlier step's true utility.  Without: the conduct is independent of theta and she
    sees the conducts only.  Her verdict is the best estimate of the step's true utility given what she has seen."""
    paths = [(F(1, 2), th, ()) for th in (0, 1)]
    for _ in range(T):
        nxt = []
        for p, th, h in paths:
            for b in (0, 1):
                pb = (F(2, 3) if b == th else F(1, 3)) if feedback else F(1, 2)
                pu1 = F(3, 4) if th == 1 else F(1, 4)
                for u in (0, 1):
                    nxt.append((p * pb * (pu1 if u else 1 - pu1), th, h + ((b, u),)))
        paths = nxt
    def seen(h, t):
        return tuple((b, u) if feedback else b for b, u in h[:t]) + (h[t][0],)
    D = []
    for t in range(T):
        num, den = {}, {}
        for p, th, h in paths:
            kk = seen(h, t)
            num[kk] = num.get(kk, F(0)) + p * h[t][1]
            den[kk] = den.get(kk, F(0)) + p
        D.append({kk: num[kk] / den[kk] for kk in num})
    out = []
    for p, th, h in paths:
        out.append((p, th, [D[t][seen(h, t)] - h[t][1] for t in range(T)]))
    return out


def r10():
    facts = {}
    ok = True
    for T in (2, 4, 6):
        runs = run_paths(T, feedback=True)
        second = sum(p * sq(sum(d) / T) for p, _, d in runs)
        sum_sq = sum(p * sum(sq(x) for x in d) for p, _, d in runs) / (T * T)
        facts["feedback, T=%d: E[mean^2]" % T] = second
        ok = ok and second == sum_sq and second <= F(1, T)
        eps = F(1, 2)
        tail = sum(p for p, _, d in runs if abs(sum(d)) >= eps * T)
        # Azuma-Hoeffding with |D_t| <= 1: tail <= 2 exp(-eps^2 T / 2), i.e. tail * exp(eps^2 T / 2) <= 2
        ok = ok and tail * _exp_upper(eps * eps * T / 2) <= 2
        facts["feedback, T=%d: P(|mean| >= 1/2)" % T] = tail
        blind = run_paths(T, feedback=False)
        facts["no feedback, T=%d: E[mean^2]" % T] = sum(p * sq(sum(d) / T) for p, _, d in blind)
    seq = [facts["feedback, T=%d: E[mean^2]" % T] for T in (2, 4, 6)]
    ok = ok and seq[0] > seq[1] > seq[2]
    # without feedback her verdict is 1/2 at every step, the best estimate given what she has seen, and
    # E[mean^2] = 1/16 + 3/(16 T): never below 1/16, so above 1/T once T > 13
    for T in (2, 4, 6):
        ok = ok and facts["no feedback, T=%d: E[mean^2]" % T] == F(1, 16) + F(3, 16 * T)
    T = 20
    binom = [F(1)]
    for n in range(T):
        binom = [F(1)] + [binom[i] + binom[i + 1] for i in range(len(binom) - 1)] + [F(1)]
    long = sum(binom[j] * F(3, 4) ** j * F(1, 4) ** (T - j) * sq(F(1, 2) - F(j, T)) for j in range(T + 1))
    facts["no feedback, T=20: E[mean^2]"] = long
    ok = ok and long == F(1, 16) + F(3, 16 * T) and long > F(1, T)
    return ("holds as a bound; fails without the feedback" if ok else "fails"), facts


# -- 11. calibrated appraisals, miscalibrated valuation ---------------------------------------
def r11():
    # (a) a product: two appraisals each the best estimate given what she observes (nothing)
    mu = {0: F(1, 2), 1: F(1, 2)}
    pts = law(mu, lambda w: 0, {0: {0: F(1)}})
    s = lambda w, b: 0
    X1 = X2 = lambda w, b: F(w)
    x1 = x2 = lambda w, b: F(1, 2)
    f = lambda a, c: a * c
    val = lambda w, b: f(x1(w, b), x2(w, b))
    Ut = lambda w, b: f(X1(w, b), X2(w, b))
    a = {"appraisals, full": [miscal(pts, x1, X1, "full", s), miscal(pts, x2, X2, "full", s)],
         "valuation": [miscal(pts, val, Ut, st, s) for st in STRENGTHS]}
    ok = a["appraisals, full"] == [0, 0] and all(v > 0 for v in a["valuation"])
    # (b) a sum: each appraisal minimally calibrated, the sum not
    s = lambda w, b: w
    X1 = lambda w, b: F(1, 5) if w == 0 else F(4, 5)
    X2 = lambda w, b: F(9, 10) if w == 0 else F(1, 10)
    x1 = X1
    x2 = lambda w, b: F(1, 2)
    val = lambda w, b: x1(w, b) + x2(w, b)
    Ut = lambda w, b: X1(w, b) + X2(w, b)
    bfacts = {"appraisals, minimal": [miscal(pts, x1, X1, "minimal", s), miscal(pts, x2, X2, "minimal", s)],
              "valuation, minimal": miscal(pts, val, Ut, "minimal", s)}
    ok = ok and bfacts["appraisals, minimal"] == [0, 0] and bfacts["valuation, minimal"] > 0
    # (c) a weighted sum of appraisals each calibrated at full strength is calibrated at full strength
    rng = random.Random(811)
    for _ in range(N_RANDOM):
        sc = rnd_scene(rng)
        p2 = law(sc["mu"], sc["k"], sc["policy"])
        Xs = [lambda w, b, a=a: sc["U"](a, w, b) for a in sc["A"]]
        xs = [cond(p2, sc["s"], X) for X in Xs]
        wts = [rnd_frac(rng) for _ in Xs]
        val = lambda w, b: sum(q * x(w, b) for q, x in zip(wts, xs))
        Ut = lambda w, b: sum(q * X(w, b) for q, X in zip(wts, Xs))
        if miscal(p2, val, Ut, "full", sc["s"]) != 0:
            ok = False
    return ("holds at every strength" if ok else "fails"), {"product": a, "sum": bfacts}


CHECKS = {"1": r1, "2": r2, "3": r3, "4": r4, "5": r5, "6": r6, "7": r7, "8": r8, "9": r9, "10": r10, "11": r11}


def run_all():
    return {k: fn() for k, fn in CHECKS.items()}


if __name__ == "__main__":
    for k, (status, facts) in run_all().items():
        print("result %s: %s" % (k, status))
        for name, v in facts.items():
            print("    %s: %s" % (name, v))
