# Hand checks cited as [checked] in bridge-dossier.md (bridge infra thread, 2026-09-02).
from fractions import Fraction as F
# (a) Two-point Stag Hunt tree: common payoff 2 if (S,S), 1 if (H,H), else 0; independent redraws.
def V(p1,p2): return 2*p1*p2 + (1-p1)*(1-p2)
base=V(0,0); worst=max(V(m,0) for m in [F(k,10) for k in range(11)])
print("V(H,H)=",base," max unilateral mixed deviation=",worst," optimum V(S,S)=",V(1,1))
# componentwise UDT_{s°,rho} at d1 with a product prior giving the other point S w.p. beta
for beta in [F(1,4),F(1,3),F(1,2)]:
    print("beta=",beta," V(pol1=S)=",2*beta," V(pol1=H)=",1-beta," -> S iff",2*beta>1-beta)
# (b) No-doubt mugging: nu(T)=1/2, occ(d)=Leaves so L(lbar)=1; D-Z bound on density = 1
nu={'T':F(1,2),'H':F(1,2)}; Ps={'T':F(1),'H':F(0)}
print("D-Z sup dP_s/dnu =",max(Ps[w]/nu[w] for w in nu)," bound =",1)
# Theorem 4.5: one anticipation atom (occ = everything), Q0 = prior-calibrated s°; density bounded
print("Thm 4.5 ||dP_s/dQ0||_inf =",max(Ps[w]/nu[w] for w in nu)," (finite: calibrated model exists)")
