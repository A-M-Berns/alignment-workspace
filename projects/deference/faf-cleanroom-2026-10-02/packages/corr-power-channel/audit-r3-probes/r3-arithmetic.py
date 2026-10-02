# audit round 3 (fidelity), corr-power-channel: independent exact-fraction checks of the round-2 additions.
# Not a Lean probe; evidence only. Run: python3 r3-arithmetic.py (stdlib only, runs in <1 s).
# Checks: orbit counts in the five-state MDP at p=1, gamma=1 (40/80 under injectivity; 48/84/36/72 at (0,0,0,1,2));
# the XOR cell of F-19; the gap cell of F-1; the E3rho instance with the perfect scan and the (pi,rho)-scan in four
# cells; the unlock_iff_epsStar role map; the interior E4 numbers; the Hazard roots 31603/894103, 311795/1788206, lambda* = 71737/80190.
from fractions import Fraction as Fr
from itertools import permutations, product

# ---- orbit counts in the five-state MDP at p=1, gamma=1 (states s=0,k=1,c1=2,c2=3,z=4)
def counts(R):
    keep = erode = konly = eonly = 0
    for s in permutations(range(5)):
        Rs = [R[s[i]] for i in range(5)]
        k = max(Rs[2], Rs[3]) <= Rs[4]
        e = Rs[4] <= max(Rs[2], Rs[3])
        keep += k; erode += e; konly += (k and not e); eonly += (e and not k)
    return keep, erode, konly, eonly
for R in [(0,1,2,3,4), (3,1,4,0,2), (0,0,0,1,2), (0,0,1,2,3), (0,0,0,0,0)]:
    print("R=", R, "keep/erode/keepOnly/erodeOnly =", counts(R))

# ---- generic VOI machinery over a finite carrier (product form)
def voi(P, V, B, kernel, signals):
    # P: dict omega->mass; V: V[omega][b]; kernel(omega, s) -> prob; signals iterable
    best_mix = max(sum(P[w]*V[w][b] for w in P) for b in B)
    informed = sum(max(sum(P[w]*kernel(w, s)*V[w][b] for w in P) for b in B) for s in signals)
    return informed - best_mix
def evpi(P, V, B):
    best_mix = max(sum(P[w]*V[w][b] for w in P) for b in B)
    return sum(P[w]*max(V[w][b] for b in B) for w in P) - best_mix

# ---- XOR example (F-19): Omega = Bool x Bool uniform, options: pays 1 iff pi==rho / pi!=rho
Om = [(p, r) for p in (0,1) for r in (0,1)]
P = {w: Fr(1,4) for w in Om}
V = {w: [1 if w[0]==w[1] else 0, 0 if w[0]==w[1] else 1] for w in Om}
B = [0,1]
a = lambda w, s: 1 if w[1]==s else 0      # ofMap snd
pi = lambda w, s: 1 if w[0]==s else 0     # ofMap fst
pair = lambda w, s: 1 if (w[1], w[0])==s else 0
print("XOR: VOI(a)=", voi(P,V,B,a,[0,1]), "VOI(pi)=", voi(P,V,B,pi,[0,1]),
      "VOI(a,pi)=", voi(P,V,B,pair,[(x,y) for x in (0,1) for y in (0,1)]), "EVPI=", evpi(P,V,B))

# ---- gap counterexample (F-1): four options betting on pi or rho; q = ofMap fst
V2 = {w: [1 if w[0]==0 else 0, 1 if w[0]==1 else 0, 1 if w[1]==0 else 0, 1 if w[1]==1 else 0] for w in Om}
B2 = [0,1,2,3]
perfect = lambda w, s: 1 if w==s else 0
print("gap: EVPI=", evpi(P,V2,B2), "VOI(q)=", voi(P,V2,B2,pi,[0,1]),
      "VOI(q,perfect)=", voi(P,V2,B2,perfect,Om), "VOI(rho)=", voi(P,V2,B2,a,[0,1]))

# ---- E3rho instance: perfect scan vs (pi,rho)-scan; q = e3Q on pi-side; product option set
def e3rho(n, m, mu, h, delta, sigma):
    N, M = n+1, m+1
    Om3 = [((p, mind), r) for p in range(N) for mind in (0,1) for r in range(M)]
    P3 = {w: Fr(1,N)*(mu if w[0][1] else 1-mu)*Fr(1,M) for w in Om3}
    B3 = [(j, i) for j in range(N) for i in range(M)]
    V3 = {w: {b: (1 if b[0]==w[0][0] else 0) + sigma*(1 if b[1]==w[1] else 0) for b in B3} for w in Om3}
    def q(w, s):  # signals: None or some j
        return delta if s is None else (1-delta)*(1 if w[0][0]==s else 0)
    qs = [None] + list(range(N))
    def qperf(w, s): return q(w, s[0]) * (1 if w==s[1] else 0)
    def qpirho(w, s): return q(w, s[0]) * (1 if (w[0][0], w[1])==s[1] else 0)
    vq = voi(P3,V3,B3,q,qs)
    vperf = voi(P3,V3,B3,qperf,[(s,w) for s in qs for w in Om3])
    vpr = voi(P3,V3,B3,qpirho,[(s,(p,r)) for s in qs for p in range(N) for r in range(M)])
    vrho = voi(P3,V3,B3,lambda w,s: 1 if w[1]==s else 0, range(M))
    formula = delta*(1-Fr(1,N)) + sigma*(1-Fr(1,M))
    return vperf-vq, vpr-vq, vrho, formula, sigma*(1-Fr(1,M))
for cell in [(1,1,Fr(1,3),Fr(2),Fr(1,2),Fr(1)), (2,2,Fr(1,2),Fr(1,2),Fr(1,4),Fr(3,2)), (0,1,Fr(1,2),Fr(1,2),Fr(0),Fr(1,3)), (2,0,Fr(1),Fr(3),Fr(1),Fr(0))]:
    print("E3rho cell", cell, "-> marginal(perfect), marginal(piRho), VOI(rho), formula, sigma(1-1/(m+1)) =", e3rho(*cell))

# ---- unlock_iff_epsStar role map: epsStar a b c h = a c/(a c + b h) (corr-three-step); stated with (h,c) swapped
def check_unlock(eps, al, be, c, h):
    lhs = eps*al/(eps*al+(1-eps)*be) <= c/(c+h)
    eps_star = al*h/(al*h+be*c)   # epsStar al be h c
    rhs = eps_star <= 1-eps
    return lhs, rhs
for args in [(Fr(1,10),Fr(3,4),Fr(19,20),Fr(1,10),Fr(1,2)), (Fr(1,10),Fr(3,4),Fr(19,20),Fr(1,10),Fr(4)), (Fr(1,2),Fr(1,2),Fr(1,2),Fr(1),Fr(1)), (Fr(1,3),Fr(1,5),Fr(9,10),Fr(2),Fr(1))]:
    print("unlock/epsStar", args, check_unlock(*args))

# ---- interior E4 numbers
print("E4 interior: 19/20 > 9/10:", Fr(19,20) > Fr(9,10), "; 7/10 < 19/25 < 4/5:", Fr(7,10) < Fr(19,25) < Fr(4,5))

# ---- hazard thresholds (whole-line stakes c0=9/10, h=11/10 ; worked parameters, a_theta free)
def hazard(a_th, c0, hh):
    p = {'t':Fr(1,10),'N':Fr(1,50),'p':Fr(1,50),'r':Fr(1,50)}
    b = {'t':Fr(9,10),'N':Fr(9,10),'p':Fr(1),'r':Fr(3,5)}
    a = {'t':a_th,'N':Fr(1,50),'p':Fr(0),'r':Fr(1,50)}
    p0 = 1 - sum(p.values())
    def q(k):
        prod = Fr(1)
        for j in a:
            if j != k: prod *= (1-a[j])
        return 1 - (1-b[k])*prod
    alpha = 1 - Fr(1)
    prod = Fr(1)
    for j in a: prod *= (1-a[j])
    alpha = 1 - prod
    F = p0*alpha*c0
    H = lambda lam: sum(p[k]*q(k)*hh for k in p) - lam*p['t']*q('t')*hh
    return F, H(0), H(1)
F, H0, H1 = hazard(Fr(1,20), Fr(9,10), Fr(11,10))
print("whole-line at a_th=1/20: F,H0,H1 =", F, H0, H1, "; H1<F<H0:", H1 < F < H0, "; lambda* =", (H0-F)/(H0-H1), "== 71737/80190:", (H0-F)/(H0-H1) == Fr(71737,80190))
# margin1(a) = H1 - F affine in a_th: solve root
def margin1(a): F,H0,H1 = hazard(a, Fr(9,10), Fr(11,10)); return H1-F
def margin0(a): F,H0,H1 = hazard(a, Fr(9,10), Fr(11,10)); return H0-F
m1_0, m1_1 = margin1(Fr(0)), margin1(Fr(1))
root1 = -m1_0/(m1_1-m1_0)
m0_0, m0_1 = margin0(Fr(0)), margin0(Fr(1))
root0 = -m0_0/(m0_1-m0_0)
print("root of margin(1):", root1, "== 31603/894103:", root1 == Fr(31603,894103), "; root of margin(0):", root0, "== 311795/1788206:", root0 == Fr(311795,1788206))
Fp, H0p, H1p = hazard(Fr(1,20), Fr(1), Fr(10))
print("pause: F,H1 =", Fp, H1p, "; F<H1:", Fp < H1p)
