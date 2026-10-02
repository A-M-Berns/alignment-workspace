#!/usr/bin/env python3
"""Adversary counterexamples for develop/general-object.md (run 3, 2026-09-14b). Exact arithmetic.
Payoffs as in the develop's Example A: three plans, three value hypotheses, V(plan_k, theta_j) = 10 if k==j else -2; null action worth 0 (N0)."""
from fractions import Fraction as F
V = [[F(10) if k == j else F(-2) for j in range(3)] for k in range(3)]
P = [F(1,2), F(1,4), F(1,4)]
def E(p, x): return sum(a*b for a, b in zip(p, x))
def post(p, k):
    pe = E(p, k); return pe, [a*b/pe for a, b in zip(p, k)]
def best(p, plans=V):
    vals = [E(p, v) for v in plans]; return vals.index(max(vals)), vals
out = []
def log(s=""): out.append(s); print(s)

log("(CE1) D11's accuracy-only reading L_Q = W_Q fails D11's own defining condition (Example A)")
Q = [F(1,5), F(3,5), F(1,5)]
aP, _ = best(P); aQ, _ = best(Q)
XQ = [V[aP][w] - V[aQ][w] for w in range(3)]
W = [w for w in range(3) if XQ[w] < 0]
for k in ([F(1,6), F(1), F(1,3)], [F(1,10), F(3,5), F(1,10)]):
    pe, pst = post(P, k)
    # condition on E_Q and W_Q
    mass = sum(P[w]*k[w] for w in W)
    condW = [P[w]*k[w]/mass if w in W else F(0) for w in range(3)]
    val_form_lhs = E(condW, XQ); val_form_rhs = E(Q, XQ)
    log(f"  k={k}: P(.|E_Q)={pst}; P(.|E_Q,W_Q)={condW} equals Q? {condW==Q}; value form: E[X_Q|E_Q,W_Q]={val_form_lhs} vs E_Q[X_Q]={val_form_rhs} equal? {val_form_lhs==val_form_rhs}")

log("\n(CE2) A source that endorses TWO targets at once (martingale family): refutes 'no kernel endorses every target' as a statement about frames")
Q1 = Q; lam = F(5,12)
Q2 = [(P[w] - lam*Q1[w])/(1-lam) for w in range(3)]
k1 = [lam*Q1[w]/P[w] for w in range(3)]; k2 = [(1-lam)*Q2[w]/P[w] for w in range(3)]
log(f"  Q1={Q1}, Q2={Q2}, lam={lam}; P == lam*Q1+(1-lam)*Q2: {[lam*Q1[w]+(1-lam)*Q2[w] for w in range(3)]==P}")
log(f"  kernels k1={k1}, k2={k2}, k1+k2={[k1[w]+k2[w] for w in range(3)]} (a partition: the source announces exactly one of Q1,Q2)")
for Qi, ki in ((Q1, k1), (Q2, k2)):
    pe, pst = post(P, ki); log(f"    announce {Qi}: P(E)={pe}, P(.|E)={pst}, equals target: {pst==Qi}")
log("  No information-inclusion structure is assumed: the agent has no private y here, and the frame is immodest by construction.")

log("\n(CE3) The button with |A|=3 under N0: the cut against the agent's own plan holds, yet the agent does not shut down (S6b, S6d, S14(1))")
k = [F(1,10), F(4,5), F(1,5)]   # overseers press more often when theta_2 (they would prefer plan 2)
pe, pst = post(P, k)
X = [V[0][w] for w in range(3)]  # X = V(a^{P_t}) - 0, a^{P_t} = plan1
cut = E(pst, X)
b, vals = best(pst)
log(f"  press kernel k={k}: P(Pr)={pe}, posterior={pst}")
log(f"  cut E[V(plan1)-0 | Pr] = {cut} (<= 0, so S6(b)'s desideratum-1 inequality holds)")
log(f"  posterior EUs of plans = {vals}; null = 0; posterior-optimal action = plan{b+1} (NOT the null action)")
log(f"  prior E[V(plan2)]={E(P,V[1])}, E[V(plan3)]={E(P,V[2])}; after the press: {vals[1]}, {vals[2]} -> the shutdown press moved the agent's beliefs about alternative plans")

log("\n(CE4) The catch-all's mass moves under ordinary Bayes (S13's 'a prior in-world evidence cannot move')")
Pold = {"o": F(9,20), "s": F(9,20), "*": F(1,10)}
lik = {"o": F(1,10), "s": F(1,10), "*": F(9,10)}   # feedback 'neither opiates nor stimulants'
Z = sum(Pold[x]*lik[x] for x in Pold)
postc = {x: Pold[x]*lik[x]/Z for x in Pold}
log(f"  prior catch-all mass eta={Pold['*']}; likelihood of the feedback={lik}; posterior={postc}; eta after = {postc['*']}")

log("\n(CE5) S8(b)'s equality clause: no decision-relevant information OFF E_Q, yet strict inequality R_t(Q) < P(E_Q)*regret")
k = [F(1,10), F(1,10), F(3,5)]; piQ = 1  # forced policy plan2
pe, pstE = post(P, k); kc = [1-x for x in k]; pn, pstN = post(P, kc)
aE, vE = best(pstE); aN, vN = best(pstN)
U = E(P, V[0]); I = pe*vE[aE] + pn*vN[aN]; M = pe*vE[piQ] + pn*vN[aN]
regret = vE[aE] - vE[piQ]
log(f"  k={k}: on E best=plan{aE+1}, off E best=plan{aN+1} (= a^P, so no decision-relevant information off E)")
log(f"  U={U}, I={I} (I>U: the push is informative ON E), M={M}; R_t(Q)=U-M={U-M}; P(E)*regret={pe*regret}; strict: {U-M < pe*regret}")

open(__file__.replace(".py", ".out"), "w").write("\n".join(out)+"\n")
