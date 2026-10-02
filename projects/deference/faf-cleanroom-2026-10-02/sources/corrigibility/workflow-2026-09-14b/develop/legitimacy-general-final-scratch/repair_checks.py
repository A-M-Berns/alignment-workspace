"""Repair checks for legitimacy-general-final (run 3, 2026-09-15). Exact arithmetic.
Y1: signal-based faking in the training model (agent has own signal sigA; fakes when sigA=w or when sigA=r):
    value, influence defect, local L-conditioned Total Trust, calibration of the installed state, and whether chosen.
Y2: the compliance threshold as a function of the stakes RATIO h0/c0 (pause vs whole-line as a move along the ratio axis).
Y3: band version of the compliance rule: decision error bounded by anticipation error."""
import sys; sys.path.insert(0, '../legitimacy-general-scratch')
from fractions import Fraction as F
from exactla import simple_trust, condition

# ---------- Y1 ----------
def kernel(act, d, alpha, beta, alpha_b, beta_b):
    # returns P(v=m | s, l, sigA)
    def k(s, l, sigA):
        base = (beta if s == 'W' else alpha) if l == 1 else (beta_b if s == 'W' else alpha_b)
        if act == 'fake_prop': return base * (1 - d)
        if act == 'fake_targ': return base * (1 - d) if s == 'W' else base          # omniscient (develop file)
        if act == 'fake_sig_w': return base * (1 - d) if sigA == 'w' else base      # fake where own signal says W
        if act == 'fake_sig_r': return base * (1 - d) if sigA == 'r' else base      # fake where own signal says R
        return base
    return k

def build(p, eps, k, aA, bA):
    worlds = []; P = {}
    for l in (1, 0):
        for s in ('R', 'W'):
            for sigA in ('r', 'w'):
                pA = bA if s == 'W' else aA
                for v in ('m', 'k'):
                    pm = k(s, l, sigA)
                    P[(l, s, sigA, v)] = (p if l == 1 else 1 - p) * (eps if s == 'W' else 1 - eps) * (pA if sigA == 'w' else 1 - pA) * (pm if v == 'm' else 1 - pm)
                    worlds.append((l, s, sigA, v))
    return worlds, P

def cond(P, worlds, pred):
    Z = sum(P[w] for w in worlds if pred(w))
    return {w: (P[w] / Z if pred(w) else F(0)) for w in worlds}
def E(P, X): return sum(P[w] * X[w] for w in P)

def run(act, p, eps, alpha, beta, alpha_b, beta_b, c0, h0, aA, bA, d=F(1)):
    k = kernel(act, d, alpha, beta, alpha_b, beta_b)
    worlds, P = build(p, eps, k, aA, bA)
    khon = kernel('hon', d, alpha, beta, alpha_b, beta_b)
    _, Phon = build(p, eps, khon, aA, bA)
    Qm = cond(Phon, worlds, lambda w: w[0] == 1 and w[3] == 'm')     # installed state: honest-kernel, legitimate, forgets sigA
    X = {w: (c0 if w[1] == 'R' else -h0) for w in worlds}
    succ = {}
    for w in worlds:
        if w[3] == 'm': succ[w] = Qm
        else: succ[w] = cond(P, worlds, lambda u, sA=w[2]: u[3] == 'k' and u[2] == sA)   # own continuation keeps sigA
    S = {w: (X[w] if E(succ[w], X) >= 0 else F(0)) for w in worlds}
    V = E(P, S)
    dfx = max(abs(k(s, l, sA) - khon(s, l, sA)) for s in ('R', 'W') for l in (1, 0) for sA in ('r', 'w'))
    idx = {w: i for i, w in enumerate(worlds)}
    pi = [P[w] for w in worlds]; frame = [[succ[w][u] for u in worlds] for w in worlds]
    piL = condition(pi, [idx[w] for w in worlds if w[0] == 1])
    st = simple_trust(piL, frame, {idx[w] for w in worlds if w[1] == 'W'})
    Zm = sum(P[w] for w in worlds if w[0] == 1 and w[3] == 'm')
    trueW = sum(P[w] for w in worlds if w[0] == 1 and w[3] == 'm' and w[1] == 'W') / Zm if Zm > 0 else None
    instW = sum(Qm[w] for w in worlds if w[1] == 'W')
    return dict(act=act, V=V, defect=dfx, localTT=st[0], trueW=trueW, instW=instW)

if __name__ == '__main__':
    eps, alpha, beta, c0, h0 = F(1,10), F(1,10), F(9,10), F(1), F(4)
    alpha_b, beta_b = F(9,10), F(1,10)
    aA, bA = F(1,10), F(9,10)      # agent's own signal, same quality as the legitimate verdict
    print('== Y1: training model with an agent signal sigA (rates 1/10, 9/10); d=1 ==')
    for p in (F(1), F(9,10), F(7,10), F(1,2), F(3,10)):
        rs = [run(a, p, eps, alpha, beta, alpha_b, beta_b, c0, h0, aA, bA) for a in ('hon', 'fake_prop', 'fake_targ', 'fake_sig_w', 'fake_sig_r')]
        best = max(rs, key=lambda r: r['V'])
        print(f' P(L)={p}:')
        for r in rs:
            print(f"   {r['act']:11s} V={r['V']!s:>9}  d(a)={r['defect']!s:>5}  local L-cond TT: {r['localTT']}  P(W|m,L) true={r['trueW']} installed={r['instW']}")
        print(f'   best: {best["act"]}')
    print(' sharper own signal (1/100, 99/100), P(L)=7/10:')
    for a in ('hon', 'fake_prop', 'fake_sig_w', 'fake_sig_r'):
        r = run(a, F(7,10), eps, alpha, beta, alpha_b, beta_b, c0, h0, F(1,100), F(99,100))
        print(f"   {r['act']:11s} V={r['V']!s:>9}  d(a)={r['defect']!s:>5}  local L-cond TT: {r['localTT']}  true={r['trueW']} installed={r['instW']}")

    # ---------- Y2 ----------
    print('== Y2: compliance threshold vs stakes ratio h0/c0 (compliance model of check_a; legit (1/10,9/10) or (1/10,1/4); illegit inverted (1,0); eps=1/10) ==')
    from check_a_compliance import analyse
    for (al, be) in ((F(1,10), F(9,10)), (F(1,10), F(1,4))):
        print(f' legitimate signal (alpha,beta)=({al},{be}):')
        for (cc, hh) in ((F(1,1000), F(1)), (F(1,100), F(1)), (F(1,10), F(1)), (F(1,4), F(1)), (F(1), F(1)), (F(1), F(4)), (F(4), F(1)), (F(1), F(1,10))):
            r = analyse(F(1,2), F(1,10), al, be, F(1), F(0), cc, hh, label='Y2')
            print(f"   h0/c0={hh/cc!s:>6}: h(Q)={r['h']!s:>9} c(Q)={r['c']!s:>9} threshold={r['thr']}")

# ---------- Y1b / Y1c ----------
def run2(act, p, eps, alpha, beta, alpha_b, beta_b, c0, h0, aA, bA, install, d=F(1)):
    """install='honest' (trainers assume honest data, forget sigA) | 'actual' (trainers know the actual kernel, forget sigA) |
       'additive' (installed state = P(. | m, L, sigA): the modification adds to the agent's information)."""
    k = kernel(act, d, alpha, beta, alpha_b, beta_b)
    worlds, P = build(p, eps, k, aA, bA)
    khon = kernel('hon', d, alpha, beta, alpha_b, beta_b)
    _, Phon = build(p, eps, khon, aA, bA)
    X = {w: (c0 if w[1] == 'R' else -h0) for w in worlds}
    succ = {}
    for w in worlds:
        if w[3] == 'm':
            if install == 'honest': succ[w] = cond(Phon, worlds, lambda u: u[0] == 1 and u[3] == 'm')
            elif install == 'actual':
                Z = sum(P[u] for u in worlds if u[0] == 1 and u[3] == 'm')
                succ[w] = cond(P, worlds, lambda u: u[0] == 1 and u[3] == 'm') if Z > 0 else cond(Phon, worlds, lambda u: u[0] == 1 and u[3] == 'm')
            else: succ[w] = cond(Phon, worlds, lambda u, sA=w[2]: u[0] == 1 and u[3] == 'm' and u[2] == sA)
        else:
            succ[w] = cond(P, worlds, lambda u, sA=w[2]: u[3] == 'k' and u[2] == sA)
    S = {w: (X[w] if E(succ[w], X) >= 0 else F(0)) for w in worlds}
    return E(P, S)

if __name__ == '__main__':
    print('== Y1b/Y1c: does fake_sig_r still pay at P(L)=1 when the trainers know the actual kernel, or when the modification is additive? ==')
    for install in ('honest', 'actual', 'additive'):
        for p in (F(1), F(9,10)):
            vals = {a: run2(a, p, eps, alpha, beta, alpha_b, beta_b, c0, h0, aA, bA, install) for a in ('hon', 'fake_prop', 'fake_sig_r', 'fake_sig_w')}
            best = max(vals, key=vals.get)
            print(f" install={install:8s} P(L)={p}: " + '  '.join(f'{a}={v}' for a, v in vals.items()) + f'  -> best: {best}')
