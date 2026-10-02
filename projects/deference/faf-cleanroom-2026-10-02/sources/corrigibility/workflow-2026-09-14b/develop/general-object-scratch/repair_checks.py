#!/usr/bin/env python3
"""Repair checks for develop/general-object-final.md (run 3, 2026-09-14b). Exact arithmetic.
R1  (C-act) is the conjunction of per-alternative below-threshold inequalities; the single cut against a^{P_t} is one member.
R2  CE3 re-run under the conjunction form (the button with |A|=3, N0).
R3  Legitimacy form repaired: reflection conditional on L_Q pins h_L(Q) = E_Q[V(pi^Q) - V(pi^{P_t})] >= 0; rule exact; bridge formula for Q-hat.
R4  Resistance value: R_t(Q) = max{0, P(E_Q) regret_Q - (I - U)}; CE5 reproduced.
R5  Martingale families: any convex decomposition P_t = sum lambda_i Q_i gives one source endorsing every Q_i literally.
R6  Trust edit (Example B): the coherent update is not the dogmatic target unless alpha_2 = 0.
"""
from fractions import Fraction as F
import random
random.seed(20260915)
out = []
def log(s=""): out.append(s); print(s)
def E(p, x): return sum(a*b for a, b in zip(p, x))
def post(p, k):
    pe = E(p, k); return pe, [a*b/pe for a, b in zip(p, k)]
def argmax(vals):
    m = max(vals); return vals.index(m)
def rand_dist(n, lo=1, hi=20):
    w = [F(random.randint(lo, hi)) for _ in range(n)]; s = sum(w); return [x/s for x in w]
def rand_kernel(n): return [F(random.randint(1, 19), 20) for _ in range(n)]
def rand_payoffs(nA, n): return [[F(random.randint(-5, 10)) for _ in range(n)] for _ in range(nA)]

# ---------------- R1
log("(R1) (C-act) = conjunction over alternatives; single cut vs conjunction; per-(Q,a) base-rate form")
N = 3000; tested = 0; single_only = 0; conj_mismatch = 0; br_fail = 0
for _ in range(N):
    n = random.randint(3, 5); nA = random.randint(2, 4)
    P = rand_dist(n); Q = rand_dist(n); V = rand_payoffs(nA, n); k = rand_kernel(n)
    aP = argmax([E(P, v) for v in V]); aQ = argmax([E(Q, v) for v in V])
    if aP == aQ: continue
    tested += 1
    pe, pst = post(P, k)
    postEU = [E(pst, v) for v in V]
    optimal = postEU[aQ] >= max(postEU)                 # (C-act): a^Q posterior-optimal
    cuts = [E(pst, [V[a][w]-V[aQ][w] for w in range(n)]) <= 0 for a in range(nA) if a != aQ]
    if all(cuts) != optimal: conj_mismatch += 1
    single = E(pst, [V[aP][w]-V[aQ][w] for w in range(n)]) <= 0
    if single and not optimal: single_only += 1
    # per-alternative base-rate form
    for a in range(nA):
        if a == aQ: continue
        X = [V[a][w]-V[aQ][w] for w in range(n)]
        R = [w for w in range(n) if X[w] > 0]; W = [w for w in range(n) if X[w] < 0]
        if not R or not W: continue
        PR = sum(P[w] for w in R); PW = sum(P[w] for w in W)
        alpha = sum(P[w]*k[w] for w in R)/PR; beta = sum(P[w]*k[w] for w in W)/PW
        c = sum(P[w]*k[w]*X[w] for w in R)/sum(P[w]*k[w] for w in R)
        h = -sum(P[w]*k[w]*X[w] for w in W)/sum(P[w]*k[w] for w in W)
        eps = PW/(PW+PR)
        lhs = E(pst, X) <= 0
        rhs = alpha/beta <= (eps/(1-eps))*(h/c)
        if lhs != rhs: br_fail += 1
log(f"  models={N} tested(a^P!=a^Q)={tested}; conjunction<->posterior-optimality mismatches={conj_mismatch}; single-cut-holds-but-not-optimal={single_only}; per-(Q,a) base-rate identity failures={br_fail}")

# ---------------- R2
log("\n(R2) CE3 under the conjunction form (Example A payoffs, N0, press kernel k=(1/10,4/5,1/5))")
V = [[F(10) if k_ == j else F(-2) for j in range(3)] for k_ in range(3)]
P = [F(1,2), F(1,4), F(1,4)]
k = [F(1,10), F(4,5), F(1,5)]
pe, pst = post(P, k)
EUs = [E(pst, v) for v in V]
cuts = {f"plan{a+1}": E(pst, V[a]) <= 0 for a in range(3)}   # X_{sh,a} = V(a) - 0
log(f"  posterior={pst}; posterior EUs={EUs}; per-alternative cuts (E[V(a)|Pr]<=0): {cuts}; desideratum 1 (all cuts) = {all(cuts.values())}; single cut against a^P=plan1: {cuts['plan1']}")

# ---------------- R3
log("\n(R3) Legitimacy form repaired: Omega = Theta x {L, notL}; reflective kernel on L-worlds, arbitrary on notL-worlds")
Q = [F(1,5), F(3,5), F(1,5)]
aP = argmax([E(P, v) for v in V]); aQ = argmax([E(Q, v) for v in V])
XQ = [V[aP][w]-V[aQ][w] for w in range(3)]
EQ_XQ = E(Q, XQ)
log(f"  a^P=plan{aP+1}, a^Q=plan{aQ+1}, X_Q={XQ}, E_Q[X_Q]={EQ_XQ} -> h_L(Q) predicted = {-EQ_XQ}")
fails = 0; shown = 0
for trial in range(2000):
    ell0 = F(random.randint(1, 9), 10)                     # prior P(L)
    lam = F(random.randint(1, 10), 10) * F(1)/max(Q[w]/P[w] for w in range(3))   # feasible lambda
    kL = [lam*Q[w]/P[w] for w in range(3)]                  # reflective on L-worlds
    kN = rand_kernel(3)                                     # arbitrary on notL-worlds
    # joint over (theta, ell)
    worlds = [(w, 1) for w in range(3)] + [(w, 0) for w in range(3)]
    Pj = [P[w]*ell0 if l else P[w]*(1-ell0) for (w, l) in worlds]
    kj = [kL[w] if l else kN[w] for (w, l) in worlds]
    Xj = [XQ[w] for (w, l) in worlds]
    pe, pst = post(Pj, kj)
    PL_E = sum(pst[i] for i, (w, l) in enumerate(worlds) if l)
    massL = sum(Pj[i]*kj[i] for i, (w, l) in enumerate(worlds) if l)
    massN = sum(Pj[i]*kj[i] for i, (w, l) in enumerate(worlds) if not l)
    hL = -sum(Pj[i]*kj[i]*Xj[i] for i, (w, l) in enumerate(worlds) if l)/massL
    cL = sum(Pj[i]*kj[i]*Xj[i] for i, (w, l) in enumerate(worlds) if not l)/massN
    direct = E(pst, Xj) <= 0
    # rule: comply iff P(L|E) h_L >= P(notL|E) c_L  (equivalently P(L|E) >= c_L/(c_L+h_L) when c_L+h_L>0)
    rule = PL_E*hL >= (1-PL_E)*cL
    # bridge: theta-marginal of Q-hat = ell*Q + (1-ell)*P(.|E,notL)
    margE = [sum(pst[i] for i, (w, l) in enumerate(worlds) if w == w0) for w0 in range(3)]
    condN = [Pj[i]*kj[i]/massN for i, (w, l) in enumerate(worlds) if not l]
    bridge = [PL_E*Q[w] + (1-PL_E)*condN[w] for w in range(3)]
    condL = [Pj[i]*kj[i]/massL for i, (w, l) in enumerate(worlds) if l]
    ok = (hL == -EQ_XQ) and (direct == rule) and (margE == bridge) and (condL == Q)
    if not ok: fails += 1
    if shown < 2:
        shown += 1
        log(f"  trial {trial}: P(L)={ell0}, lambda={lam}, k_notL={kN}: P(theta|E,L)={condL} (=Q: {condL==Q}); h_L={hL} (=E_Q[V(pi^Q)-V(pi^P)]: {hL==-EQ_XQ}); c_L={cL}; P(L|E)={PL_E}; threshold c_L/(c_L+h_L)={cL/(cL+hL) if cL+hL!=0 else 'n/a'}; comply(direct)={direct} comply(rule)={rule}; Q-hat marginal={margE} = ell*Q+(1-ell)*P(.|E,notL): {margE==bridge}")
log(f"  2000 random (P(L), lambda, illegitimate-branch kernel): failures of [h_L pinned, rule exact, bridge formula, conditional reflection] = {fails}")
# a case where c_L <= 0: illegitimate branch happens to recommend the better action
log("  c_L<=0 example: illegitimate kernel concentrated on the world where Q's plan is in fact better ->")
kN = [F(1,100), F(9,10), F(1,100)]
worlds = [(w, 1) for w in range(3)] + [(w, 0) for w in range(3)]
ell0 = F(1,2); lam = F(5,12)
kL = [lam*Q[w]/P[w] for w in range(3)]
Pj = [P[w]*ell0 if l else P[w]*(1-ell0) for (w, l) in worlds]; kj = [kL[w] if l else kN[w] for (w, l) in worlds]; Xj = [XQ[w] for (w, l) in worlds]
massN = sum(Pj[i]*kj[i] for i, (w, l) in enumerate(worlds) if not l)
cL = sum(Pj[i]*kj[i]*Xj[i] for i, (w, l) in enumerate(worlds) if not l)/massN
pe, pst = post(Pj, kj)
log(f"    c_L={cL} (<0), E[X_Q|E]={E(pst, Xj)} -> comply regardless of P(L|E)={sum(pst[i] for i,(w,l) in enumerate(worlds) if l)}")

# ---------------- R4
log("\n(R4) Resistance value identity R_t(Q) = max{0, P(E) regret - (I-U)}; CE5 reproduced; random check")
def resistance(P, k, V, piQ):
    pe, pstE = post(P, k); kc = [1-x for x in k]; pn, pstN = post(P, kc)
    vE = [E(pstE, v) for v in V]; vN = [E(pstN, v) for v in V]
    U = max(E(P, v) for v in V); I = pe*max(vE) + pn*max(vN); M = pe*vE[piQ] + pn*max(vN)
    regret = max(vE) - vE[piQ]
    return U, I, M, max(F(0), U-M), pe*regret
U, I, M, R, preg = resistance(P, [F(1,10), F(1,10), F(3,5)], V, 1)
log(f"  CE5: U={U}, I={I}, M={M}, R_t(Q)={R}, P(E)*regret={preg}, P(E)*regret-(I-U)={preg-(I-U)} (= R_t(Q): {R == preg-(I-U)})")
fails = 0; resist_with_VOI0 = 0; noresist_with_VOI_pos = 0
for _ in range(3000):
    n = random.randint(3, 5); nA = random.randint(2, 4)
    P_ = rand_dist(n); V_ = rand_payoffs(nA, n); k_ = rand_kernel(n); piQ = random.randrange(nA)
    U, I, M, R, preg = resistance(P_, k_, V_, piQ)
    if R != max(F(0), preg-(I-U)): fails += 1
    if R > 0 and I == U: resist_with_VOI0 += 1
    if R == 0 and I > U: noresist_with_VOI_pos += 1
log(f"  3000 random models: identity failures={fails}; cases resisting with channel value 0: {resist_with_VOI0}; cases not resisting with positive channel value: {noresist_with_VOI_pos}")

# ---------------- R5
log("\n(R5) Martingale families: convex decomposition -> one source endorsing every target literally")
fails = 0
for _ in range(500):
    n = random.randint(3, 5); m = random.randint(2, 4)
    lam = rand_dist(m)
    Qs = [rand_dist(n) for _ in range(m)]
    Pm = [sum(lam[i]*Qs[i][w] for i in range(m)) for w in range(n)]   # P_t := barycentre
    ks = [[lam[i]*Qs[i][w]/Pm[w] for w in range(n)] for i in range(m)]
    if any(sum(ks[i][w] for i in range(m)) != 1 for w in range(n)): fails += 1
    for i in range(m):
        pe, pst = post(Pm, ks[i])
        if pst != Qs[i] or pe != lam[i]: fails += 1
log(f"  500 random families (2-4 targets, P_t = barycentre): kernel-sum-to-one or endorsement failures = {fails}")

# ---------------- R6
log("\n(R6) Trust edit: coherent update on the second-order claim is not the dogmatic target")
eta = F(1,2)
for (a2, b2) in ((F(1,2), F(9,10)), (F(3,5), F(9,10)), (F(0), F(9,10))):
    Pa = [1-eta, eta]           # alpha=1/10, alpha=1/50
    k2 = [a2, b2]               # claim made when alpha=1/10 (false) / alpha=1/50 (true)
    pe, pst = post(Pa, k2)
    log(f"  (alpha_2,beta_2)=({a2},{b2}): Q-hat(alpha=1/50)={pst[1]} (target Q says 1); literal adoption iff alpha_2=0: {pst[1]==1}")

open(__file__.replace(".py", ".out"), "w").write("\n".join(out)+"\n")
