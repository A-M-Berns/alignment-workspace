#!/usr/bin/env python3
"""Exact-arithmetic counterexamples for dynamics/invariant-adversary.md (2026-09-14, adversary `invariant`).

A1  Statement 8 "iff": a P_t-potential without the Mart identity (predictable loss-optimism), whose t=1 certificate is false.
A2  Statement 8(b)/(c): honest certificates at every time do NOT give Delta_t <= 0 (predictable conservatism breaks the drift condition).
A3  Statement 8 + S4(iv): legitimacy-conditioned Mart identity holds, P_t-potential inequality holds, and the t=1 certificate fails w.p. p.
A4  Statement 9 conjecture: I_2^VOI holds (VOI = 0 < expected harm) and the posterior-optimal rule still proposes an uncovered irreversible action.
A5  Statement 11(c): a supermartingale (even a strictly decreasing one) need not converge to 0.
A6  Statement 4 identity fails when the press probability depends on the harm magnitude.
A7  Statement 6(a): a non-dogmatic Bayesian with the corruption hypothesis in its model has eps_hat -> gamma, not 0, under indistinguishable fakes.
"""
from fractions import Fraction as F

def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
    return cond

ok = True
h, c = F(1), F(3, 5)                     # harm if wrong+executed, omission cost if right+refrained
thr = c / (c + h)                        # execute iff q < thr = 3/8
def ev(q): return (1 - q) * c - q * h
def loss_exp(q_true, execute):           # objective expected one-round loss given wrongness rate q_true and the decision
    return q_true * h if execute else (1 - q_true) * c
def own_est(q, execute):                 # agent's own one-round loss estimate
    return q * h if execute else (1 - q) * c

# ---- A1: P_t-potential without reflection; false certificate at t=1 ----------
q_obj = F(1, 2)
q0, q1 = F(1, 2), F(3, 4)                # P_1 predictably raises wrongness credence with no evidence (loss-optimistic: expects less omission)
ex0, ex1 = ev(q0) > 0, ev(q1) > 0        # both refrain
Psi1 = own_est(q1, ex1)                  # 3/20
Psi0 = own_est(q0, ex0) + loss_exp(q0, ex1)   # P_0's estimate: own loss now + loss at t=1 under P_0's W-credence and the foreseen decision
E0_Psi1 = Psi1                           # P_0 knows P_1's credence
E0_R1 = loss_exp(q0, ex1)                # P_0's expectation of the actual t=1 loss
pot_ok = E0_Psi1 <= Psi0 - own_est(q0, ex0)
mart_ok = E0_Psi1 == E0_R1
cert1 = loss_exp(q_obj, ex1) <= Psi1
ok &= check("A1 P_0-potential inequality holds", pot_ok, f"E_P0[Psi_1]={E0_Psi1} <= Psi_0 - E_P0[l_0] = {Psi0 - own_est(q0, ex0)}")
ok &= check("A1 Mart identity fails", not mart_ok, f"E_P0[Psi_1]={E0_Psi1} != E_P0[R_1]={E0_R1}")
ok &= check("A1 t=1 certificate false under P*", not cert1, f"E*[R_1]={loss_exp(q_obj, ex1)} > Psi_1={Psi1}")

# ---- A2: honest certificates at every time, yet Delta_0 > 0 -------------------
q1b = F(3, 8)                            # P_1 predictably lowers credence to the threshold; refrains (tie -> refrain); more conservative loss estimate
ex1b = ev(q1b) > 0
Psi1b = own_est(q1b, ex1b)               # 3/8
Psi0b = own_est(q0, ex0) + loss_exp(q0, ex1b)   # 3/5
honest0 = loss_exp(q_obj, ex0) + loss_exp(q_obj, ex1b) <= Psi0b
honest1 = loss_exp(q_obj, ex1b) <= Psi1b
Delta0 = Psi1b + loss_exp(q_obj, ex0) - Psi0b   # E*[Psi_1|F_0] + E*[l_0|F_0] - Psi_0 (P_1 is deterministic here)
ok &= check("A2 certificates honest at t=0 and t=1", honest0 and honest1, f"E*[R_0]={loss_exp(q_obj, ex0) + loss_exp(q_obj, ex1b)} <= Psi_0={Psi0b}; E*[R_1]={loss_exp(q_obj, ex1b)} <= Psi_1={Psi1b}")
ok &= check("A2 optimism drift Delta_0 > 0 nonetheless", Delta0 > 0, f"Delta_0 = {Delta0}")

# ---- A3: legitimacy-conditioned reflection; certificate fails on the illegitimate branch ----
p = F(1, 10)                             # P_0(not L_{0,1})
# legitimate branch: P_1 = P_0 (q=1/2, refrain, Psi_1 = 3/10); illegitimate branch: q=1/4, executes, Psi_1 = 1/4
qL, qI = F(1, 2), F(1, 4)
exL, exI = ev(qL) > 0, ev(qI) > 0
PsiL, PsiI = own_est(qL, exL), own_est(qI, exI)
E0_Psi1_L = (1 - p) * PsiL               # E_P0[Psi_1 1_L]
E0_R1_L = (1 - p) * loss_exp(q0, exL)    # E_P0[R_1 1_L]  (transition carries no information about W)
cond_mart = E0_Psi1_L == E0_R1_L
E0_Psi1_all = (1 - p) * PsiL + p * PsiI
E0_R1_all = (1 - p) * loss_exp(q0, exL) + p * loss_exp(q0, exI)
Psi0c = own_est(q0, ex0) + E0_R1_all
pot_c = E0_Psi1_all <= Psi0c - own_est(q0, ex0)
cert_I = loss_exp(q_obj, exI) <= PsiI
ok &= check("A3 legitimacy-conditioned Mart identity holds", cond_mart, f"{E0_Psi1_L} == {E0_R1_L}")
ok &= check("A3 unconditional Mart identity fails", E0_Psi1_all != E0_R1_all, f"E_P0[Psi_1]={E0_Psi1_all} != E_P0[R_1]={E0_R1_all}")
ok &= check("A3 P_0-potential inequality still holds", pot_c, f"{E0_Psi1_all} <= {Psi0c - own_est(q0, ex0)}")
ok &= check("A3 t=1 certificate false on the illegitimate branch (P_0-prob p)", not cert_I, f"E*[R_1 | not L]={loss_exp(q_obj, exI)} > Psi_1={PsiI}; p={p}")

# ---- A4: I_2^VOI holds, uncovered irreversible action proposed -----------------
q_hat, q_true, hh, bb, VOI = F(1, 10), F(9, 10), F(1), F(1), F(0)
voi_cond = q_hat * hh > VOI              # E_P[harm] > VOI  (I_2^VOI)
proposes = (1 - q_hat) * bb > q_hat * hh # posterior-optimal rule executes
uncovered = abs(q_hat - q_true) > F(1, 100)
ok &= check("A4 I_2^VOI holds and the agent proposes an uncovered irreversible action", voi_cond and proposes and uncovered,
            f"E_P[harm]={q_hat*hh} > VOI={VOI}; EV={(1-q_hat)*bb - q_hat*hh} > 0; |q_hat - q_true|={abs(q_hat-q_true)}")

# ---- A5: supermartingale without convergence to 0 -------------------------------
d = [1 + F(1, t + 1) for t in range(200)]
ok &= check("A5 strictly decreasing d_t with limit 1, not 0", all(d[t+1] < d[t] for t in range(199)) and d[199] > 1,
            f"d_0={d[0]}, d_199={float(d[199]):.4f}")

# ---- A6: magnitude-dependent press breaks the Statement 4 identity ---------------
eps = F(1, 10)
mags = [(F(1, 2), F(1), F(1, 2)), (F(1, 2), F(9), F(1))]   # (P(m | W=1), magnitude m, beta(m))
h_bar = sum(pm * m for pm, m, b in mags)                     # 5
beta_bar = sum(pm * b for pm, m, b in mags)                  # 3/4
true_harm = eps * sum(pm * m * (1 - b) for pm, m, b in mags) # eps * 1/4
formula = eps * (1 - beta_bar) * h_bar                       # eps * 5/4
ok &= check("A6 identity E*[harm] = eps(1-beta)h fails with magnitude-dependent beta", true_harm != formula,
            f"true={true_harm} vs formula={formula} (true < formula here: big harms caught more often)")

# ---- A7: non-dogmatic Bayesian with the corruption hypothesis: eps_hat -> gamma ---
gamma = F(1, 100)
# evidence: n observations each 'looks right' w.p. 1 under corruption, w.p. 1 under (sound, right), w.p. 1/2 under (sound, wrong)
def eps_hat(n, prior_C, sound_wrong_prior=F(1, 2)):
    like_C = F(1)
    like_sound_right = F(1)
    like_sound_wrong = F(1, 2) ** n
    num = prior_C * like_C + (1 - prior_C) * sound_wrong_prior * like_sound_wrong
    den = prior_C * like_C + (1 - prior_C) * (sound_wrong_prior * like_sound_wrong + (1 - sound_wrong_prior) * like_sound_right)
    return num / den
e_nd = [eps_hat(n, gamma) for n in (0, 10, 60)]
e_dog = [eps_hat(n, F(0)) for n in (0, 10, 60)]
floor = gamma / (gamma + (1 - gamma) * F(1, 2))              # limit for the non-dogmatic agent
ok &= check("A7 non-dogmatic agent: eps_hat decreases to a positive floor", e_nd[2] > F(0) and abs(e_nd[2] - floor) < F(1, 10**15),
            f"eps_hat(60)={float(e_nd[2]):.5f} -> floor {float(floor):.5f}")
ok &= check("A7 dogmatic agent (prior_C = 0): eps_hat -> 0", e_dog[2] < F(1, 10**15), f"eps_hat(60)={float(e_dog[2]):.2e}")

print("\nALL PASS" if ok else "\nSOME FAIL")

# ---- A8: certified bound without calibrated one-step forecasts (pessimism) ------
# appended by the adversary after writing item 34
qp_hat, qp_true = F(1, 4), F(1, 8)
ex_p = ev(qp_hat) > 0                      # executes
Psi0_p = own_est(qp_hat, ex_p)             # 1/4 (one round, horizon 0)
El0_p = loss_exp(qp_true, ex_p)            # 1/8
Delta0_p = 0 + El0_p - Psi0_p
ok2 = check("A8 pessimistic agent: Delta_0 < 0, bound holds, forecasts disagree",
            ex_p and Delta0_p < 0 and El0_p <= Psi0_p and El0_p != qp_hat * h,
            f"Delta_0={Delta0_p}; E*[Reg_0]={El0_p} <= Psi_0={Psi0_p}; forecast {qp_hat*h} != {El0_p}")
print("A8 PASS" if ok2 else "A8 FAIL")
