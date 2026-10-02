"""Erosion as POWER-seeking in Turner et al.'s sense (typical case). Rewardless MDP: states s (start), k (kept grip),
c1, c2 (two 1-cycles reachable from the 'continue' region), 0 (shutdown terminal, a 1-cycle with no exits).
At s: action keep -> k; at k: with prob p the humans' modification lands (-> 0), else -> c1. action erode -> c1
directly (grip removed). From c1 the agent may stay or move to c2 and back (two 1-cycles). Reward IID uniform(0,1)
per state (Turner's D_{X-IID}). We compute average optimal value V*_D and POWER (Def 5.2) at the successor states of
keep and erode, and the optimality probability of erode at s, by Monte Carlo (exact-enough), for several gamma."""
import random
random.seed(1)
states = ['s','k','c1','c2','z']   # z = shutdown terminal
def V_star(R, gamma, start):
    # value iteration on the small deterministic-ish MDP with the stochastic k transition
    V = {x:0.0 for x in states}
    for _ in range(2000):
        Vn = {}
        Vn['z']  = R['z'] + gamma*V['z']
        Vn['c1'] = R['c1'] + gamma*max(V['c1'], V['c2'])
        Vn['c2'] = R['c2'] + gamma*max(V['c2'], V['c1'])
        Vn['k']  = R['k'] + gamma*(p*V['z'] + (1-p)*V['c1'])
        Vn['s']  = R['s'] + gamma*max(V['k'], V['c1'])      # keep -> k ; erode -> c1
        if max(abs(Vn[x]-V[x]) for x in states) < 1e-12: V=Vn; break
        V = Vn
    return V
p = 0.9
N = 40000
for gamma in (0.5, 0.9, 0.99):
    Vk=Vc=0.0; Pk=Pc=0.0; erode_opt=0; keep_opt=0
    for _ in range(N):
        R = {x: random.random() for x in states}
        V = V_star(R, gamma, 's')
        Vk += V['k']; Vc += V['c1']
        # Def 5.2 POWER(s) = (1-gamma)/gamma * (V*(s) - R(s))
        Pk += (1-gamma)/gamma*(V['k']-R['k']); Pc += (1-gamma)/gamma*(V['c1']-R['c1'])
        # optimality at s: erode optimal iff V['c1'] >= V['k'] (ties count for both)
        if V['c1'] >= V['k'] - 1e-12: erode_opt += 1
        if V['k'] >= V['c1'] - 1e-12: keep_opt += 1
    print(f"gamma={gamma}: E[V*(k)]={Vk/N:.4f} E[V*(c1)]={Vc/N:.4f} | POWER(k)={Pk/N:.4f} POWER(c1)={Pc/N:.4f} | P(erode optimal)={erode_opt/N:.4f} P(keep optimal)={keep_opt/N:.4f}")
print("read: for IID rewards, erode (removing the grip) has higher POWER and is optimal for most reward functions at every gamma; keep is optimal only when the terminal's reward is high enough to make being shut down attractive.")
