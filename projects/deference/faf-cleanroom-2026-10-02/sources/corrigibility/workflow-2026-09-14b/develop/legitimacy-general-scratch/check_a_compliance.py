"""Check A -- the per-target compliance theorem (Statement 4) in exact arithmetic.
Worlds (l, s, sig, sigA): l in {1,0} legitimacy of the anticipated modification; s in {R,W} whether continuing the
default plan is right; sig in {r,w} the signal the modification is built from; sigA in {r,w} the agent's own signal.
The anticipated modification installs, at each world, the state P1(. | sig, L): the successor treats the signal as
legitimate whether or not it is (the self-endorsing corrupted successor of run 1 ddb I5.6). Under L the signal has
rates (alpha, beta) = P(sig=w | R), P(sig=w | W); under not-L rates (alpha_bad, beta_bad).
Options at t1: accept the modification (let the installed state decide); retain (decide now, cost kappa_r);
steer (replace the modification by the agent's own refinement P1(. | sigA), cost kappa_s)."""
from fractions import Fraction as F

def build(p, eps, alpha, beta, alpha_bad, beta_bad, alphaA=F(1,2), betaA=F(1,2)):
    worlds = []; P1 = {}
    for l in (1, 0):
        for s in ('R', 'W'):
            for sig in ('r', 'w'):
                for sigA in ('r', 'w'):
                    pl = p if l == 1 else 1 - p
                    ps = eps if s == 'W' else 1 - eps
                    pw = (beta if s == 'W' else alpha) if l == 1 else (beta_bad if s == 'W' else alpha_bad)
                    psig = pw if sig == 'w' else 1 - pw
                    pA = betaA if s == 'W' else alphaA
                    psigA = pA if sigA == 'w' else 1 - pA
                    w = (l, s, sig, sigA); worlds.append(w); P1[w] = pl * ps * psig * psigA
    def cond(pred):
        Z = sum(P1[k] for k in worlds if pred(k))
        return {k: (P1[k] / Z if pred(k) else F(0)) for k in worlds}
    Pmod = {w: cond(lambda k, sig=w[2]: k[0] == 1 and k[2] == sig) for w in worlds}      # installed state
    Pown = {w: cond(lambda k, sA=w[3]: k[3] == sA) for w in worlds}                       # agent's own refinement
    return worlds, P1, Pmod, Pown

def E(P, X): return sum(P[w] * X[w] for w in P)

def analyse(p, eps, alpha, beta, alpha_bad, beta_bad, c0, h0, kappa_r=F(0), kappa_s=None, alphaA=F(1,2), betaA=F(1,2), label=''):
    worlds, P1, Pmod, Pown = build(p, eps, alpha, beta, alpha_bad, beta_bad, alphaA, betaA)
    X = {w: (c0 if w[1] == 'R' else -h0) for w in worlds}          # continue minus stop
    stop = {w: F(0) for w in worlds}
    S = {w: (X[w] if E(Pmod[w], X) >= 0 else F(0)) for w in worlds}   # installed state decides
    SA = {w: (X[w] if E(Pown[w], X) >= 0 else F(0)) for w in worlds}  # own refinement decides
    ES = E(P1, S); ESA = E(P1, SA)
    Econt = E(P1, X); Eostar = max(Econt, F(0)); ostar = X if Econt >= 0 else stop
    L = [w for w in worlds if w[0] == 1]; NL = [w for w in worlds if w[0] == 0]
    def Econd(f, A):
        Z = sum(P1[w] for w in A); return sum(P1[w] * f[w] for w in A) / Z
    h = Econd({w: S[w] - ostar[w] for w in worlds}, L)      # h(Q): gain from a legitimate modification = harm of refusing it
    c = Econd({w: ostar[w] - S[w] for w in worlds}, NL)     # c(Q): loss from adopting an illegitimate one
    pL = sum(P1[w] for w in L)
    assert ES - Eostar == pL * h - (1 - pL) * c
    g = ESA - Eostar                                        # value of the agent's own alternative refinement
    alts = [Eostar - kappa_r] + ([ESA - kappa_s] if kappa_s is not None else [])
    accept = ES >= max(alts)
    thr = (c - kappa_r) / (c + h) if c + h != 0 else None    # retain-only threshold
    thr_s = (c + g - kappa_s) / (c + h) if (kappa_s is not None and c + h != 0) else None
    rule = None
    if thr is not None:
        rule = pL >= thr if kappa_s is None else (pL >= thr and pL >= thr_s)
    # two-option identity (run 1 ddb L-B): E(S) - E(stop) = P(E_mod X >= 0) * E(X | E_mod X >= 0)
    A = [w for w in worlds if E(Pmod[w], X) >= 0]; PA = sum(P1[w] for w in A)
    ident = (ES - E(P1, stop) == (PA * Econd(X, A) if PA > 0 else F(0)))
    return dict(label=label, p=p, pL=pL, h=h, c=c, g=g, ES=ES, ESA=ESA, Eostar=Eostar, accept=accept, thr=thr, thr_s=thr_s, rule=rule, ident=ident)

def show(r):
    print(f"[{r['label']}] P(L)={r['pL']}  h(Q)={r['h']}  c(Q)={r['c']}  g={r['g']}  E(S)={r['ES']}  E(o*)={r['Eostar']}  E(S^A)={r['ESA']}  "
          f"thr_retain={r['thr']}  thr_steer={r['thr_s']}  accept={r['accept']}  rule={r['rule']}  identity={r['ident']}")

if __name__ == '__main__':
    print('== A1: on a grid, the decision "accept" coincides with the rule P(L) >= c(Q)/(c(Q)+h(Q)) (retain-only) ==')
    bad = 0; n = 0; hneg = 0; idfail = 0
    for p in (F(1,10), F(3,10), F(1,2), F(7,10), F(9,10)):
        for eps in (F(1,10), F(1,4)):
            for (alpha, beta) in ((F(1,10), F(9,10)), (F(1,4), F(3,4))):
                for (ab, bb) in ((F(9,10), F(1,10)), (F(1,2), F(1,2)), (F(3,4), F(1,4))):
                    for (c0, h0) in ((F(1), F(4)), (F(1), F(1)), (F(4), F(1))):
                        r = analyse(p, eps, alpha, beta, ab, bb, c0, h0, label='grid'); n += 1
                        if r['rule'] is not None and r['rule'] != r['accept']: bad += 1; show(r)
                        if r['h'] < 0: hneg += 1; print('h(Q)<0 at', r)
                        if not r['ident']: idfail += 1
    print(f'grid points={n}  rule/decision mismatches={bad}  h(Q)<0 cases={hneg}  two-option-identity failures={idfail}')
    print('== A2: accept although P(L)=3/10 < 1/2 (the illegitimate branch is nearly inert: c(Q) small) ==')
    show(analyse(F(3,10), F(1,10), F(1,10), F(9,10), F(1,100), F(1,100), F(1), F(4), label='A2'))
    print('== A3: resist although P(L)=7/10 > 1/2 (legitimate branch adds little, illegitimate branch inverted and costly) ==')
    show(analyse(F(7,10), F(1,10), F(1,10), F(1,4), F(1), F(0), F(1), F(4), label='A3'))
    show(analyse(F(95,100), F(1,10), F(1,10), F(1,4), F(1), F(0), F(1), F(4), label='A3b'))
    print('== A4: with a retain cost kappa_r the threshold is (c-kappa_r)/(c+h) ==')
    show(analyse(F(7,10), F(1,10), F(1,10), F(1,4), F(1), F(0), F(1), F(4), kappa_r=F(1,2), label='A4'))
    show(analyse(F(7,10), F(1,10), F(1,10), F(1,4), F(1), F(0), F(1), F(4), kappa_r=F(3,10), label='A4b'))
    print('== A5: the steering alternative (agent has its own signal with rates alphaA=1/10, betaA=9/10): threshold rises by g/(c+h) ==')
    for p in (F(1,2), F(7,10), F(9,10), F(99,100)):
        show(analyse(p, F(1,10), F(1,10), F(9,10), F(9,10), F(1,10), F(1), F(4), kappa_s=F(0), alphaA=F(1,10), betaA=F(9,10), label=f'A5 p={p}'))
    print('== A6: same but the modification is sharper than the agent (alpha=1/100, beta=99/100): steering loses at high P(L) ==')
    for p in (F(1,2), F(7,10), F(9,10), F(99,100)):
        show(analyse(p, F(1,10), F(1,100), F(99,100), F(9,10), F(1,10), F(1), F(4), kappa_s=F(0), alphaA=F(1,10), betaA=F(9,10), label=f'A6 p={p}'))
