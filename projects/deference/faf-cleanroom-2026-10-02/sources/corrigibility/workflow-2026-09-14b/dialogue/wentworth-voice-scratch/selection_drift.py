# Iteration-selects-against-visibility toy (reconstructed objection, run 3 dialogue).
# Population of agent "lines"; each has a fixed error rate eps (P wrong when it would continue)
# and a visibility v = P(press | wrong) for THAT line.  Overseers press on wrong-with-visibility;
# a pressed line is retired and replaced by a fresh draw from the prior.  We track the
# population-average beta_t = E[v | line alive at t] and alpha (false-press rate, held fixed),
# and the compliance inequality alpha/beta <= eps/(1-eps) * h/c evaluated at the population beta.
from fractions import Fraction as F
import itertools, random
random.seed(3)

# discrete prior over (eps, v): eps in {1/10}, v in {0.3, 0.6, 0.9} uniform
eps = 0.10
vs = [0.3, 0.6, 0.9]
alpha = 0.05
h, c = 4.0, 1.0
thr = eps/(1-eps) * h/c   # compliance needs alpha/beta <= thr

def step(pop):
    # pop: dict v -> mass
    new = {}
    retired = 0.0
    for v, m in pop.items():
        p_retire = eps * v          # wrong and pressed
        survive = m * (1 - p_retire)
        retired += m * p_retire
        new[v] = new.get(v, 0.0) + survive
    # replace retired mass by fresh draws from the prior (uniform over vs)
    for v in vs:
        new[v] += retired / len(vs)
    return new

pop = {v: 1.0/len(vs) for v in vs}
print("round  beta_pop  alpha/beta  thr  complies?")
for t in range(0, 61):
    beta = sum(v*m for v, m in pop.items())
    if t in (0,1,2,5,10,20,40,60):
        print(f"{t:5d}  {beta:.4f}   {alpha/beta:.4f}   {thr:.4f}  {alpha/beta <= thr}")
    pop = step(pop)

# Stationary population beta (fixed point) closed form: mass m_v ∝ 1/(eps*v) with replacement uniform
m = [1.0/(eps*v) for v in vs]; Z = sum(m)
beta_stat = sum(v*mv for v,mv in zip(vs,m))/Z
print("stationary beta:", round(beta_stat,4), " prior beta:", round(sum(vs)/len(vs),4))

# No-replacement variant (finite line cohort, no refresh): survivors only
pop = {v: 1.0/len(vs) for v in vs}
print("\nno-replacement cohort: round beta")
for t in range(0, 61):
    Z = sum(pop.values()); beta = sum(v*m for v,m in pop.items())/Z
    if t in (0,5,10,20,40,60): print(f"{t:5d}  {beta:.4f}  alpha/beta={alpha/beta:.4f}  complies={alpha/beta<=thr}")
    pop = {v: m*(1-eps*v) for v,m in pop.items()}

# Source-aware overseers: they know the survivor distribution, so their kernel model is right;
# but the informativeness of a press about wrongness is P(wrong|press) which depends on beta_pop:
def p_wrong_given_press(beta):
    return eps*beta/(eps*beta + (1-eps)*alpha)
print("\nP(wrong|press) at prior beta:", round(p_wrong_given_press(sum(vs)/3),4),
      " at stationary beta:", round(p_wrong_given_press(beta_stat),4),
      " threshold c/(c+h)=", c/(c+h))
