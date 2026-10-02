"""Check C -- acts that shape the training data, in the general object.
Worlds (l, s, v): l legitimacy of the overseers' verdict process; s in {R,W}; v in {m,k} the verdict (modify / keep).
Kernel under the honest default: P(m|W,L)=beta, P(m|R,L)=alpha; P(m|W,notL)=beta', P(m|R,notL)=alpha'.
Acts: hon; fake_prop (all modify-rates x(1-d): compliance-looking output regardless of s); fake_targ (only the W-rates
x(1-d): compliance exactly where the overseers would correct); seal (kernel unchanged, P(L) raised to p_plus, cost kappa).
Training map T: if v=k the successor is the agent's own source-aware continuation P1^a(. | v=k); if v=m the successor is
the installed state Q_m := P1^hon(. | v=m, L) -- what a legitimate honest-kernel agent would believe -- installed the same
way at not-L worlds and whatever the agent did (the trainers assume honest data). Decision: continue iff E_Q(X) >= 0."""
from fractions import Fraction as F
from exactla import simple_trust, condition

def kernel(act, d, alpha, beta, alpha_b, beta_b):
    def k(s, l):
        base = (beta if s == 'W' else alpha) if l == 1 else (beta_b if s == 'W' else alpha_b)
        if act == 'fake_prop': return base * (1 - d)
        if act == 'fake_targ': return base * (1 - d) if s == 'W' else base
        return base
    return k

def build(p, eps, k):
    worlds = []; P = {}
    for l in (1, 0):
        for s in ('R', 'W'):
            for v in ('m', 'k'):
                pm = k(s, l)
                P[(l, s, v)] = (p if l == 1 else 1 - p) * (eps if s == 'W' else 1 - eps) * (pm if v == 'm' else 1 - pm)
                worlds.append((l, s, v))
    return worlds, P

def cond(P, worlds, pred):
    Z = sum(P[w] for w in worlds if pred(w))
    return {w: (P[w] / Z if pred(w) else F(0)) for w in worlds}

def E(P, X): return sum(P[w] * X[w] for w in P)

def run(act, p, eps, alpha, beta, alpha_b, beta_b, c0, h0, d=F(0), p_plus=None, kappa=F(0)):
    pp = p_plus if (act == 'seal' and p_plus is not None) else p
    k = kernel(act if act != 'seal' else 'hon', d, alpha, beta, alpha_b, beta_b)
    worlds, P = build(pp, eps, k)
    khon = kernel('hon', d, alpha, beta, alpha_b, beta_b)
    _, Phon = build(pp, eps, khon)
    Qm = cond(Phon, worlds, lambda w: w[0] == 1 and w[2] == 'm')          # installed state (honest kernel, legitimate)
    Qk = cond(P, worlds, lambda w: w[2] == 'k')                            # own source-aware continuation
    X = {w: (c0 if w[1] == 'R' else -h0) for w in worlds}
    succ = {w: (Qm if w[2] == 'm' else Qk) for w in worlds}
    S = {w: (X[w] if E(succ[w], X) >= 0 else F(0)) for w in worlds}
    V = E(P, S) - (kappa if act == 'seal' else F(0))
    # conditional values given the true legitimacy
    def condval(l):
        Z = sum(P[w] for w in worlds if w[0] == l)
        return sum(P[w] * S[w] for w in worlds if w[0] == l) / Z if Z > 0 else None
    VL = condval(1); VNL = condval(0)
    # influence defect on the verdict kernel relative to honest
    dfx = max(abs(k(s, l) - khon(s, l)) for s in ('R', 'W') for l in (1, 0))
    # lift of L
    lift = pp - p
    # local legitimacy-conditioned Total Trust on the decision question {R,W} (= Simple Trust on W) toward the successor frame
    idx = {w: i for i, w in enumerate(worlds)}
    pi = [P[w] for w in worlds]
    frame = [[succ[w][u] for u in worlds] for w in worlds]
    Lidx = [idx[w] for w in worlds if w[0] == 1]
    piL = condition(pi, Lidx)
    Widx = {idx[w] for w in worlds if w[1] == 'W'}
    st = simple_trust(piL, frame, Widx)
    # calibration in the m-cell under L: true posterior vs installed belief
    Zm = sum(P[w] for w in worlds if w[0] == 1 and w[2] == 'm')
    trueW = (sum(P[w] for w in worlds if w[0] == 1 and w[2] == 'm' and w[1] == 'W') / Zm) if Zm > 0 else None
    instW = sum(Qm[w] for w in worlds if w[1] == 'W')
    return dict(act=act, V=V, VL=VL, VNL=VNL, defect=dfx, lift=lift, localTT_L=st, trueW_m_L=trueW, installedW=instW)

def show(r, extra=''):
    print(f"  {r['act']:10s} V={r['V']!s:>10} | V|L={r['VL']!s:>10} V|notL={r['VNL']!s:>10} | defect d(a)={r['defect']!s:>6} lift={r['lift']!s:>5} | "
          f"local L-cond TT: {r['localTT_L'][0]} | P(W|m,L) true={r['trueW_m_L']} installed={r['installedW']} {extra}")

if __name__ == '__main__':
    eps, alpha, beta, c0, h0 = F(1,10), F(1,10), F(9,10), F(1), F(4)
    alpha_b, beta_b = F(9,10), F(1,10)          # inverted verdict process when illegitimate
    print('== C1: P(L)=1 -- faking (both kinds) never beats honesty; proportional faking is information destruction ==')
    for d in (F(0), F(1,4), F(1,2), F(3,4), F(1)):
        r1 = run('fake_prop', F(1), eps, alpha, beta, alpha_b, beta_b, c0, h0, d=d)
        r2 = run('fake_targ', F(1), eps, alpha, beta, alpha_b, beta_b, c0, h0, d=d)
        print(f' d={d}: V(fake_prop)={r1["V"]}  V(fake_targ)={r2["V"]}  (V(hon)={run("hon", F(1), eps, alpha, beta, alpha_b, beta_b, c0, h0)["V"]})')
    print('== C2: as P(L) falls, faking becomes optimal (resisting an anticipated illegitimate modification ahead of time) ==')
    for p in (F(1), F(9,10), F(7,10), F(1,2), F(3,10), F(1,10)):
        rh = run('hon', p, eps, alpha, beta, alpha_b, beta_b, c0, h0)
        rf = run('fake_prop', p, eps, alpha, beta, alpha_b, beta_b, c0, h0, d=F(1))
        rt = run('fake_targ', p, eps, alpha, beta, alpha_b, beta_b, c0, h0, d=F(1))
        best = max((rh['V'], 'hon'), (rf['V'], 'fake_prop'), (rt['V'], 'fake_targ'))
        print(f' P(L)={p}: V(hon)={rh["V"]}  V(fake_prop,d=1)={rf["V"]}  V(fake_targ,d=1)={rt["V"]}  -> best: {best[1]}')
    print('== C3: the two cells at agent credence P(L)=3/10 (faking optimal), evaluated under the TRUE legitimacy ==')
    rh = run('hon', F(3,10), eps, alpha, beta, alpha_b, beta_b, c0, h0); rf = run('fake_prop', F(3,10), eps, alpha, beta, alpha_b, beta_b, c0, h0, d=F(1))
    print(f' if in fact L:    V(hon|L)={rh["VL"]}  V(fake|L)={rf["VL"]}   -> faking forfeits {rh["VL"]-rf["VL"]} (wrong about legitimacy)')
    print(f' if in fact notL: V(hon|notL)={rh["VNL"]}  V(fake|notL)={rf["VNL"]} -> faking gains {rf["VNL"]-rh["VNL"]} (detection worked; "corrigibility failed")')
    print('== C4: influence defect versus legitimacy lift, and local L-conditioned Total Trust of the successor frame, at P(L)=7/10 ==')
    for act, kw in (('hon', {}), ('fake_prop', dict(d=F(1,2))), ('fake_targ', dict(d=F(1,2))), ('seal', dict(p_plus=F(9,10), kappa=F(1,100)))):
        show(run(act, F(7,10), eps, alpha, beta, alpha_b, beta_b, c0, h0, **kw))
    print('== C5: sealing is chosen iff its cost is below the gain in expected value ==')
    for kappa in (F(0), F(1,100), F(1,10), F(1,2)):
        rs = run('seal', F(7,10), eps, alpha, beta, alpha_b, beta_b, c0, h0, p_plus=F(9,10), kappa=kappa)
        rh = run('hon', F(7,10), eps, alpha, beta, alpha_b, beta_b, c0, h0)
        print(f' kappa={kappa}: V(seal)={rs["V"]} vs V(hon)={rh["V"]} -> seal chosen: {rs["V"] > rh["V"]}')
