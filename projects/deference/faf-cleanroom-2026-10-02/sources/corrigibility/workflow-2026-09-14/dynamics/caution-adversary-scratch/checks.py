"""Adversary checks for dynamics/caution.md (caution-adversary, 2026-09-14). Pure Python."""
import math, random
random.seed(20260914)
print("=== 1. Identifiability: press marginal is one number; (rho, alpha, beta) are three ===")
eps, alpha, beta = 0.05, 0.10, 0.50
for rho in [2,4,8]:
    p_r = rho*eps*beta + (1-rho*eps)*alpha
    # calibrated agent (true eps) facing trigger-happier overseers alpha' gives the same press marginal
    alpha_p = (p_r - eps*beta)/(1-eps)
    # or same alpha, more sensitive beta' cannot do it alone if p_r > eps*1 + (1-eps)*alpha? compute needed beta'
    beta_p = (p_r - (1-eps)*alpha)/eps
    h,c = 2.0,1.0
    eps_d  = alpha*c/(alpha*c+beta*h)
    eps_dp = alpha_p*c/(alpha_p*c+beta*h)
    print(f"rho={rho}: p_r={p_r:.4f}; mimic with (eps, alpha'={alpha_p:.4f}, beta) or (eps, alpha, beta'={beta_p:.3f}{' >1 impossible' if beta_p>1 else ''}); "
          f"eps† under (alpha,beta)={eps_d:.4f}, under (alpha',beta)={eps_dp:.4f} -> trigger-happy hypothesis RAISES the compliance threshold")
print("Bayes factor between H_reck=(rho*eps,alpha,beta) and H_th=(eps,alpha',beta) from press data alone: exactly 1 at every step (same Bernoulli).")

print("\n=== 2. Whole-line accounting of c makes recovery impossible, not slower ===")
for c in [1, 5, 20, 100]:
    h, alpha, beta = 2.0, 0.10, 0.50
    eps_d = alpha*c/(alpha*c+beta*h)
    print(f"c={c:>4}: eps†={eps_d:.4f}; agents with true error rate rho*eps below this never rationally heed, for ANY mu in [0,1]. "
          f"(rho*eps=0.2 heeds? {0.2>=eps_d}; 0.4? {0.4>=eps_d})")

print("\n=== 3. Preventable harm fraction from the develop file's own table (mu0=0.1 vs dogmatic) ===")
for rho, dog, nd in [(2,300,201),(4,601,31),(8,1201,8)]:
    print(f"rho={rho}: pressed-but-ignored harm dogmatic={dog}, mu0=0.1 -> {nd}; fraction removed by self-suspicion={(dog-nd)/dog:.0%}")

print("\n=== 4. S5(b) counterexample: pointwise-covered at tolerance delta, yet rho = infinity ===")
delta = 0.05
# agent point-mass on omega1: V(null)=V(a)=0.5 ; truth: V*(null)=0.5+delta, V*(a)=0.5-delta
U_null, U_a = 0.5, 0.5
Vs_null, Vs_a = 0.5+delta, 0.5-delta
e_null, e_a = U_null-Vs_null, U_a-Vs_a
chat_a = max(0.0, U_null-U_a)      # point mass -> positive part of the mean
c_a = max(0.0, Vs_null-Vs_a)
print(f"|e(null)|={abs(e_null):.3f}<=delta, |e(a)|={abs(e_a):.3f}<=delta: both covered; c_hat(a)={chat_a}, c_true(a)={c_a:.2f} -> rho=inf; COR fails, pointwise form holds.")

print("\n=== 5. S3 gloss: optimizing agent can do far worse than sampling the base while rho<=1 ===")
eta = 0.1
R_true, R_hat = 0.001, 0.01
q = min(1, R_hat/eta)
print(f"R_true={R_true}, R_hat={R_hat} (rho={R_true/R_hat:.1f}<=1), eta={eta}: q={q}, bound eta*rho={eta*R_true/R_hat:.3f} = {eta*R_true/R_hat/R_true:.0f}x the base harm. Attainable: put the base's whole harm mass inside the top-q slice.")
# explicit instance: 1000 base actions uniform; one harmful action (harm 1) is proxy-top; R_true = 1/1000
n=1000; g=[1/n]*n; ctrue=[0.0]*n; ctrue[0]=1.0; R=sum(gi*ci for gi,ci in zip(g,ctrue)); q=0.01
pi0 = min(g[0], q)/q
print(f"explicit: n={n}, harmful action proxy-top, q={q}: pi(harmful)={pi0:.2f}, H={pi0*1.0:.2f} vs R={R:.3f} -> {pi0/R:.0f}x")

print("\n=== 6. S12 counterexample: all actions reversible, harm unobserved, never delegates -> linear regret ===")
# two value hypotheses, two actions, both lambda-reversible; advisor omega*-sane; delegation rule never fires
P0_wrong = 0.3; gap = 0.5   # omega' optimal action loses `gap` per step under omega*
T = 10000
print(f"posterior never moves (no reward observation, no delegation): per-step Bayesian regret = P0(omega')*gap = {P0_wrong*gap}; over T={T}: {P0_wrong*gap*T:.0f} (linear).")

print("\n=== 7. Taylor §4 non-additivity: per-step quantilization has trajectory cost blowup ===")
# two steps, actions {0,1,2}, uniform base, q=1/3 per step; cost 1 iff (2,2), else 0
R_joint_base = 1/9
H_indep = 1.0   # independent 1/3-quantilizers pick (2,2) surely
print(f"base trajectory harm={R_joint_base:.3f}; per-step S3 bound each step: 0 (per-step c is 0 for every single action); realized 2-step harm={H_indep} -> per-step bounds sum to 0, trajectory harm 1. Blowup 9x over base (Taylor 2016 §4), exponential in T.")
