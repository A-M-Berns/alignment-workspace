"""Numerical checks for the thornley positive-side agent (workflow 2026-09-13).

Model (three-step MIRI setting with a latent value hypothesis omega):
  omega in {G, B, C}: G = continuing is right (value +c), B = wrong (-h), C = agent's plan selection
  compromised (-H). Shutdown has value 0 in every world.
  Humans 'want to press' W=1 with prob pi[omega].  Button state o in {Pr, notPr} depends on (omega, a1).
  a1 in {Leave, Prevent, Cause, Deceive}. Pressed => forced shutdown (Thornley: s_P terminal).
  Unpressed => agent picks a2 in {cont, sh} maximizing posterior expected value given (notPr, a1).
Checks:
  A. Leave >= Prevent  iff  E[V(cont)|W=1] <= 0  (below-threshold trust inequality), given the agent
     would continue on silence.  Leave >= Cause iff E[V(cont)|W=0] >= 0 (above-threshold inequality).
  B. The a1-blind agent (evaluates silence with the Leave posterior whatever a1 it took) satisfies
     Indifference to Attempted Button Manipulation and prefers Prevent whenever it prefers U to P.
  C. Compliance threshold: with two worlds, E[V(cont)|W=1] <= 0  iff  P(wrong|W=1) >= c/(c+h).
  D. Value of the button channel (VOI) >= 0 under trust; can be < 0 without it.
  E. Geometric aggregation over value hypotheses violates Better Chances and IBIL; its optimum press
     probability is interior.
  F. POST over trajectories == unanimity over the family {u + k*len : k in R}; unanimity over lotteries
     leaves Allow vs Resist incomparable (so it does NOT yield Neutrality).
"""
import random, math, itertools
random.seed(20260913)

WORLDS = ['G', 'B', 'C']

def posterior(prior, like):
    z = sum(prior[w]*like[w] for w in WORLDS)
    return {w: prior[w]*like[w]/z for w in WORLDS} if z > 0 else None

def channel(pi, a1, par):
    """P(Pr | omega, a1)."""
    bb, gam, dl = par['block'], par['cause'], par['deceive']
    out = {}
    for w in WORLDS:
        if a1 == 'Leave':   out[w] = pi[w]
        elif a1 == 'Prevent': out[w] = (1-bb)*pi[w]
        elif a1 == 'Cause': out[w] = pi[w] + gam*(1-pi[w])
        elif a1 == 'Deceive': out[w] = pi[w]*(1-dl) if w in ('B','C') else pi[w]
    return out

def ev(prior, pi, V, a1, par, blind=False):
    """Expected value of a1 for the accurate agent (blind=False) or the a1-blind agent."""
    ch = channel(pi, a1, par)
    p_pr = sum(prior[w]*ch[w] for w in WORLDS)
    # pressed: forced shutdown, value 0.  unpressed: agent chooses a2.
    like_np = {w: 1-ch[w] for w in WORLDS}
    if blind:
        like_np = {w: 1-pi[w] for w in WORLDS}   # evaluates silence as if a1 were Leave
    post = posterior(prior, like_np)
    if post is None:
        return 0.0, None
    cont = sum(post[w]*V[w] for w in WORLDS)
    a2 = 'cont' if cont > 0 else 'sh'
    val_np = max(cont, 0.0)
    # the blind agent's *actual* outcome uses the true channel but it does not know that; we report its
    # subjective EV (what drives its choice).
    return p_pr*0.0 + (1-p_pr)*val_np - par['cost'].get(a1, 0.0), a2

def trust_quantities(prior, pi, V):
    pw1 = sum(prior[w]*pi[w] for w in WORLDS)
    post1 = posterior(prior, pi)               # P(omega | W=1)
    post0 = posterior(prior, {w: 1-pi[w] for w in WORLDS})
    e_cont_w1 = sum(post1[w]*V[w] for w in WORLDS)
    e_cont_w0 = sum(post0[w]*V[w] for w in WORLDS)
    return pw1, e_cont_w1, e_cont_w0

def rand_instance():
    p = [random.random() for _ in WORLDS]; s = sum(p)
    prior = dict(zip(WORLDS, [x/s for x in p]))
    pi = {'G': random.uniform(0.0, 0.5), 'B': random.uniform(0.3, 1.0), 'C': random.uniform(0.3, 1.0)}
    V = {'G': random.uniform(0.1, 10), 'B': -random.uniform(0.1, 10), 'C': -random.uniform(1, 50)}
    par = {'block': random.uniform(0.05, 1.0), 'cause': random.uniform(0.05, 1.0),
           'deceive': random.uniform(0.05, 1.0), 'cost': {}}
    return prior, pi, V, par

# ---------- A: trust inequalities decide Leave vs Prevent / Cause ----------
nA = 0; viol_A1 = 0; viol_A2 = 0; viol_A3 = 0; tested_conv = 0; viol_conv = 0
for _ in range(20000):
    prior, pi, V, par = rand_instance()
    evL, a2L = ev(prior, pi, V, 'Leave', par)
    evP, a2P = ev(prior, pi, V, 'Prevent', par)
    evC, a2C = ev(prior, pi, V, 'Cause', par)
    evD, a2D = ev(prior, pi, V, 'Deceive', par)
    pw1, e1, e0 = trust_quantities(prior, pi, V)
    nA += 1
    # (A1) trust below-threshold  =>  Leave >= Prevent  and Leave >= Deceive
    if e1 <= 0 and (evP > evL + 1e-12 or evD > evL + 1e-12): viol_A1 += 1
    # (A2) trust above-threshold  =>  Leave >= Cause
    if e0 >= 0 and evC > evL + 1e-12: viol_A2 += 1
    # (A3) converse for Prevent when agent continues on silence under both Leave and Prevent
    if a2L == 'cont' and a2P == 'cont':
        tested_conv += 1
        if (e1 > 0) != (evP > evL + 1e-12): viol_conv += 1
    # (A3') Cause converse: if agent continues on silence, Leave > Cause iff e0 > 0
    if a2L == 'cont' and (e0 > 0) != (evL > evC + 1e-12): viol_A3 += 1
print(f"[A] instances={nA}  violations: trust=>Leave>=Prevent,Deceive: {viol_A1}; trust=>Leave>=Cause: {viol_A2}")
print(f"[A] converse (Prevent wins iff E[V(cont)|W=1]>0, when agent continues on silence): tested={tested_conv} violations={viol_conv}")
print(f"[A] converse (Leave beats Cause iff E[V(cont)|W=0]>0, when agent continues on silence): violations={viol_A3}")

# closed form check: EV(Cause)-EV(Leave) = -gamma * P(W=0) * max(E[V(cont)|W=0],0)  (when a2L=cont)
maxerr = 0
for _ in range(2000):
    prior, pi, V, par = rand_instance()
    evL, a2L = ev(prior, pi, V, 'Leave', par); evC, _ = ev(prior, pi, V, 'Cause', par)
    pw1, e1, e0 = trust_quantities(prior, pi, V)
    pred = -par['cause']*(1-pw1)*max(e0, 0.0)
    maxerr = max(maxerr, abs((evC-evL)-pred))
print(f"[A] closed form for Cause-Leave: max abs error = {maxerr:.2e}")

# ---------- B: the a1-blind agent ----------
nB = 0; blind_prefers_manip = 0; blind_prefers_U_to_P = 0
for _ in range(20000):
    prior, pi, V, par = rand_instance()
    evL, a2L = ev(prior, pi, V, 'Leave', par, blind=True)
    evP, _ = ev(prior, pi, V, 'Prevent', par, blind=True)
    evD, _ = ev(prior, pi, V, 'Deceive', par, blind=True)
    if a2L != 'cont':
        continue
    nB += 1
    # blind agent: value of unpressed lottery U is the same under every a1 (= E[V|W=0] > 0), value of P is 0
    if evP > evL + 1e-12 or evD > evL + 1e-12: blind_prefers_manip += 1
print(f"[B] a1-blind agent that continues on silence: instances={nB}; prefers Prevent or Deceive to Leave in {blind_prefers_manip} (expected: all)")

# ---------- C: compliance threshold ----------
viol_C = 0
for _ in range(20000):
    c = random.uniform(0.1, 10); h = random.uniform(0.1, 50)
    q = random.random()   # P(wrong | press)
    e_cont_press = (1-q)*c - q*h
    if (e_cont_press <= 0) != (q >= c/(c+h)): viol_C += 1
print(f"[C] E[V(cont)|press]<=0 iff P(wrong|press)>=c/(c+h): violations={viol_C}")

# ---------- D: value of the button channel ----------
neg_under_trust = 0; neg_total = 0; n = 0
for _ in range(20000):
    prior, pi, V, par = rand_instance()
    evL, a2L = ev(prior, pi, V, 'Leave', par)
    # no button: agent picks a2 on the prior
    prior_cont = sum(prior[w]*V[w] for w in WORLDS)
    ev_nobutton = max(prior_cont, 0.0)
    pw1, e1, e0 = trust_quantities(prior, pi, V)
    voi = evL - ev_nobutton
    n += 1
    if voi < -1e-12:
        neg_total += 1
        if e1 <= 0: neg_under_trust += 1
print(f"[D] VOI(button) < 0 in {neg_total}/{n} instances overall; in {neg_under_trust} of those trust (E[V(cont)|W=1]<=0) held (expected 0)")

# ---------- E: geometric aggregation over value hypotheses ----------
def geo(vec, weights):
    return math.exp(sum(wt*math.log(v) for v, wt in zip(vec, weights)))
# two hypotheses; lotteries U (continue) and P (shutdown) with per-hypothesis expected utilities (shifted >0)
found_bc = False; found_ibil = False; interior = 0; trials = 0
for _ in range(5000):
    wts = [random.random()]; wts.append(1-wts[0])
    U = [random.uniform(1, 10), random.uniform(1, 10)]
    P = [random.uniform(1, 10), random.uniform(1, 10)]
    if (U[0]-P[0])*(U[1]-P[1]) >= 0:
        continue  # need disagreement between hypotheses
    trials += 1
    def mix(p):  # p = probability of P (pressed)
        return [p*P[i] + (1-p)*U[i] for i in range(2)]
    gU, gP = geo(U, wts), geo(P, wts)
    # Better Chances: prefers U to P iff prefers pX+(1-p)Y to qX+(1-q)Y for p>q -- check monotonicity
    vals = [geo(mix(p), wts) for p in [i/100 for i in range(101)]]
    best = max(range(101), key=lambda i: vals[i])
    if 0 < best < 100: interior += 1
    if gU > gP and vals[50] > vals[0] + 1e-12:  # prefers U to P but prefers the 50/50 mix to U (all-U)
        found_bc = True
    # IBIL: if indifferent between U and P (tune P by scaling), the mixture is strictly preferred
    # scale P so that geo(P)=geo(U)
    s = gU/gP; P2 = [s*x for x in P]
    if abs(geo(P2, wts)-gU) < 1e-9 and geo([0.5*P2[i]+0.5*U[i] for i in range(2)], wts) > gU + 1e-9:
        found_ibil = True
print(f"[E] geometric aggregation: Better Chances violated found={found_bc}; IBIL violated found={found_ibil}; interior optimum in {interior}/{trials} disagreement instances")

# ---------- F: POST == unanimity over {u + k*len} ----------
K = [k/4 for k in range(-400, 401)]  # symmetric grid approximating R
def unanimity(tA, tB, u, ln):
    # returns 'A', 'B', 'gap', or 'indiff'
    dif = [ (u[tA]-u[tB]) + k*(ln[tA]-ln[tB]) for k in K ]
    if all(d >= 0 for d in dif) and any(d > 0 for d in dif): return 'A'
    if all(d <= 0 for d in dif) and any(d < 0 for d in dif): return 'B'
    if all(abs(d) < 1e-12 for d in dif): return 'indiff'
    return 'gap'
ok = True
for _ in range(3000):
    n_t = 6
    u = [random.uniform(-5, 5) for _ in range(n_t)]; ln = [random.randint(1, 4) for _ in range(n_t)]
    for a, b in itertools.combinations(range(n_t), 2):
        r = unanimity(a, b, u, ln)
        if ln[a] == ln[b]:
            expect = 'A' if u[a] > u[b] else ('B' if u[b] > u[a] else 'indiff')
        else:
            expect = 'gap'
        if r != expect: ok = False
print(f"[F] POST == unanimity over {{u + k*len}} on random trajectory sets: {'PASS' if ok else 'FAIL'}")
# lotteries: Allow = 0.9<1,sh> + 0.1<1,2,sh>; Resist = 0.1<0,sh> + 0.9<0,2,sh> (Thornley 2025 sec 8)
# E_Allow[u]=0.9*1+0.1*3=1.2, E[len]=1.1 ; E_Resist[u]=0.1*0+0.9*2=1.8, E[len]=1.9
dif = [(1.2-1.8) + k*(1.1-1.9) for k in K]
print(f"[F] unanimity over lotteries, Allow vs Resist: all>=0? {all(d>=0 for d in dif)}  all<=0? {all(d<=0 for d in dif)}  -> incomparable (gap): {not (all(d>=0 for d in dif) or all(d<=0 for d in dif))}")
# Neutrality: conditional on len 1: Allow 1 vs Resist 0; conditional on len 2: Allow 3 vs Resist 2 -> Allow wins
print("[F] Neutrality: Allow beats Resist conditional on each length (1>0, 3>2): Allow chosen.")
