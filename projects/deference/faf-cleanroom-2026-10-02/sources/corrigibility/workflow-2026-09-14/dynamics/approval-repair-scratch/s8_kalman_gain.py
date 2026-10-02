"""S8 repair check (adversary A8.2): a Bayesian (Kalman) learner tracking a drifting target.
Target theta*_t random walk with process variance q_true = sstar^2; observation theta*_t + noise, var R = sxi^2.
Learner A models drift correctly (q_model = q_true): steady-state gain > 0, never freezes.
Learner B models no drift (q_model = 0): gain -> 0, estimate freezes, error grows like sqrt(t).
"""
import random, math
random.seed(7)
sstar=0.02; sxi=0.05; q_true=sstar**2; R=sxi**2
def run(q_model,T):
    ths=0.0; mu=0.0; P=1.0; errs=[]; gains=[]
    for t in range(T):
        ths+=random.gauss(0,sstar)
        y=ths+random.gauss(0,sxi)
        P=P+q_model
        K=P/(P+R)
        mu=mu+K*(y-mu); P=(1-K)*P
        errs.append(abs(mu-ths)); gains.append(K)
    return errs,gains
for T in [600,6000]:
    for name,q in [("drift-in-model",q_true),("no-drift-in-model",0.0)]:
        E=[];G=[]
        for _ in range(100):
            e,g=run(q,T); E.append(e[-1]); G.append(g[-1])
        print(f"T={T:5d} {name:18s} final gain K_T = {sum(G)/len(G):.4f}   mean final |error| = {sum(E)/len(E):.3f}")
# steady-state gain, closed form: P_ss solves P = (P+q)R/(P+q+R) -> P^2 + qP - qR = 0
Pss=(-q_true+math.sqrt(q_true**2+4*q_true*R))/2
print(f"closed-form steady-state gain with drift in model: K_ss = {(Pss+q_true)/(Pss+q_true+R):.4f}")
