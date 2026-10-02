#!/usr/bin/env python3
"""Exact-arithmetic checks for dynamics/invariant.md (2026-09-14, develop agent `invariant`).

Every check prints PASS/FAIL. Fractions throughout; no floats except for display.

C1  Harmonic hazard: prod_{t<T} (1 - 1/(t+2)) == 1/(T+1)  (catastrophe a.s. as T -> inf)
C2  Geometric hazard: 1 - prod(1-d_t) <= sum d_t (union bound), and sum d_t = Delta for d_t = Delta * 2^-(t+1)
C3  Compliance threshold with fixed stakes: alpha=1/20, beta=1, c=1, h=20, eps_t = 2^-t  -> first failing t
C4  Growing stakes h_t = 2^t * h keep condition (i) forever (eps_t*h_t constant)
C5  Corruption floor: gamma=1/100; agent's subjective eps_hat_t = 2^-t; objective eps_t >= gamma;
    harm with subjective rule (defies from t0) grows linearly; harm with residual rule <= sum eps_t(1-beta)h
C6  Predictable-optimism two-period example: reflection gap and failed re-certification at t=1
C7  Statement 4 identity on a 3-round toy: expected harm under compliance vs defiance
C8  Monotone descent vs convergence: d_t=(1+(-1)^t/2)/(t+1) converges, not monotone
C9  Moving target: tracking rate vs target speed (three regimes)
C10 Statement 5(a): constant eps*h does not by itself propagate condition (i); the (1-eps)-free form does
"""
from fractions import Fraction as F

def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + ("  " + detail if detail else ""))
    return cond

ok = True

# ---- C1 harmonic hazard ------------------------------------------------------
def harmonic_survival(T):
    p = F(1)
    for t in range(T):
        p *= (1 - F(1, t + 2))
    return p
for T in (1, 2, 5, 10, 100, 1000):
    ok &= check(f"C1 harmonic survival T={T}", harmonic_survival(T) == F(1, T + 1),
                f"prod = {harmonic_survival(T)}")
# limit form holds: d_t -> 0; rate form fails: sum diverges. Survival 1/(T+1) -> 0.

# ---- C2 geometric hazard, union bound ---------------------------------------
Delta = F(1, 10)
def geo(t): return Delta * F(1, 2 ** (t + 1))
for T in (1, 5, 20):
    hit = 1 - eval("*".join(["1"] + [f"(1-geo({t}))" for t in range(T)]))
    s = sum(geo(t) for t in range(T))
    ok &= check(f"C2 union bound T={T}", hit <= s and s <= Delta,
                f"1-prod={float(hit):.6f} <= sum={float(s):.6f} <= Delta={float(Delta)}")

# ---- C3 compliance threshold, fixed stakes ----------------------------------
alpha, beta, c, h = F(1, 20), F(1), F(1), F(20)
def cond_i(eps, h_t, c_t, a=alpha, b=beta):
    # alpha/beta <= eps/(1-eps) * h/c   <=>  eps*h*b >= (1-eps)*c*a
    return eps * h_t * b >= (1 - eps) * c_t * a
first_fail = None
for t in range(0, 40):
    eps = F(1, 2 ** t)
    if not cond_i(eps, h, c):
        first_fail = t
        break
ok &= check("C3 first failing round with fixed stakes", first_fail == 9, f"t0 = {first_fail} (2^t <= 401 iff t <= 8)")
# posterior wrongness given press at t0-1 and t0
def post_wrong(eps, a=alpha, b=beta):
    return eps * b / (eps * b + (1 - eps) * a)
thr = c / (c + h)
ok &= check("C3 posterior at t=8 clears threshold", post_wrong(F(1, 256)) >= thr,
            f"{float(post_wrong(F(1,256))):.5f} >= {float(thr):.5f}")
ok &= check("C3 posterior at t=9 below threshold", post_wrong(F(1, 512)) < thr,
            f"{float(post_wrong(F(1,512))):.5f} <  {float(thr):.5f}")

# ---- C4 growing stakes -------------------------------------------------------
all_hold = all(cond_i(F(1, 2 ** t), h * 2 ** t, c) for t in range(0, 60))
ok &= check("C4 growing stakes h_t = 2^t h: condition (i) holds for t<60", all_hold,
            "eps_t*h_t = h constant, (1-eps_t)*c*alpha <= c*alpha = 1/20 < 20")

# ---- C5 corruption floor -----------------------------------------------------
gamma = F(1, 100)
beta5 = F(9, 10)
T = 1000
# subjective rule: agent uses eps_hat_t = 2^-t; defies once cond_i(eps_hat) fails
# objective eps_t = gamma + (1-gamma)*2^-t  (corrupted rounds are wrong w.p. 1; sound rounds wrong w.p. 2^-t)
harm_subjective = F(0); harm_residual = F(0); t_defy = None
for t in range(T):
    eps_hat = F(1, 2 ** t) if t < 60 else F(0)
    eps_obj = gamma + (1 - gamma) * eps_hat
    complies_subj = cond_i(eps_hat, h, c, b=beta5)
    if not complies_subj and t_defy is None: t_defy = t
    complies_res = cond_i(max(eps_hat, gamma), h, c, b=beta5)
    harm_subjective += eps_obj * (1 - (beta5 if complies_subj else 0)) * h
    harm_residual += eps_obj * (1 - (beta5 if complies_res else 0)) * h
ok &= check("C5 subjective rule defies from finite t0", t_defy is not None and t_defy < 20, f"t0 = {t_defy}")
ok &= check("C5 subjective-rule harm grows linearly (>= gamma*h*(T-t0-1))",
            harm_subjective >= gamma * h * (T - t_defy - 1),
            f"harm_subj over T={T}: {float(harm_subjective):.2f}; gamma*h*(T-t0-1) = {float(gamma*h*(T-t_defy-1)):.2f}")
ok &= check("C5 residual rule complies throughout and harm bounded by sum eps_t(1-beta)h",
            harm_residual <= sum((gamma + (1 - gamma) * F(1, 2 ** min(t, 60))) * (1 - beta5) * h for t in range(T)),
            f"harm_res over T={T}: {float(harm_residual):.2f} (per-round floor gamma*(1-beta)*h = {float(gamma*(1-beta5)*h):.3f})")
ok &= check("C5 residual condition (i) with eps=gamma", cond_i(gamma, h, c, b=beta5),
            f"alpha/beta = {float(alpha/beta5):.4f} <= gamma/(1-gamma)*h/c = {float(gamma/(1-gamma)*h/c):.4f}")

# ---- C6 predictable optimism (reflection failure) ---------------------------
# one harmful-if-wrong action; objective wrongness 1/2; h=1, c=3/5.
h6, c6, q_obj = F(1), F(3, 5), F(1, 2)
q0, q1 = F(1, 2), F(1, 4)     # P_0 is calibrated; P_1 predictably drops to 1/4 with no evidence
def ev_execute(q): return (1 - q) * c6 - q * h6   # value of executing relative to null
exec0 = ev_execute(q0) > 0; exec1 = ev_execute(q1) > 0
ok &= check("C6 refrain at t=0, execute at t=1", (not exec0) and exec1,
            f"EV0={ev_execute(q0)}, EV1={ev_execute(q1)}")
# losses: t=0 refrain -> omission cost (1-W)*c ; t=1 execute -> harm W*h
Psi1 = q1 * h6                         # agent's own estimate of l_1 at t=1
true_R1 = q_obj * h6                   # objective expected l_1
Psi0 = (1 - q0) * c6 + q0 * h6         # P_0 foresees: refrain now (omission if right), execute next (harm if wrong)
true_R0 = (1 - q_obj) * c6 + q_obj * h6
ok &= check("C6 t=0 certificate holds", true_R0 <= Psi0, f"E*[R_0]={true_R0} <= Psi_0={Psi0}")
ok &= check("C6 t=1 certificate fails", true_R1 > Psi1, f"E*[R_1]={true_R1} >  Psi_1={Psi1}")
# reflection (Mart form) on R_1: E_{P_0}[Psi_1] should equal E_{P_0}[R_1] = q0*h
ok &= check("C6 reflection gap", Psi1 != q0 * h6, f"E_P0[Psi_1]={Psi1} != E_P0[R_1]={q0*h6}")

# ---- C7 Statement 4 identity on a 3-round toy --------------------------------
rounds = [(F(1, 10), F(9, 10), F(1, 20), F(20), F(1)),   # (eps, beta, alpha, h, c)
          (F(1, 50), F(4, 5),  F(1, 20), F(30), F(2)),
          (F(1, 200), F(1, 2), F(1, 100), F(50), F(3))]
harm_c = sum(e * (1 - b) * hh for e, b, a, hh, cc in rounds)
omit_c = sum((1 - e) * a * cc for e, b, a, hh, cc in rounds)
harm_d = sum(e * hh for e, b, a, hh, cc in rounds)
ok &= check("C7 compliance harm < defiance harm; omission cost positive", harm_c < harm_d and omit_c > 0,
            f"harm_c={float(harm_c):.4f} harm_d={float(harm_d):.4f} omit_c={float(omit_c):.4f}")

# ---- C8 convergence without monotone descent --------------------------------
d = [(1 + F((-1) ** t, 2)) / (t + 1) for t in range(12)]
mono = all(d[t + 1] <= d[t] for t in range(11))
ok &= check("C8 d_t converges (d_11 small) but is not monotone", (not mono) and d[11] < F(1, 10),
            "d = " + ", ".join(f"{float(x):.3f}" for x in d[:6]) + ", ...")

# ---- C9 moving target: tracking rate vs target speed -------------------------
def track(d0, r, v, T):
    d = F(d0)
    for t in range(T):
        d = max(F(0), d - r(t) + v(t))
    return d
rA = lambda t: F(1, t + 2)                 # tracking rate decays like a learning rate
vA = lambda t: F(1, 10)                    # target drifts at constant speed
vB = lambda t: F(1, (t + 2) ** 2)          # target drift summable
vC = lambda t: F(1, t + 2)                 # target drift equals tracking rate
dA = [track(1, rA, vA, T) for T in (10, 100, 1000)]
dB = [track(3, rA, vB, T) for T in (10, 100, 1000)]   # d_0 = 3 so the descent is visible before it clamps at 0
dC = [track(1, rA, vC, T) for T in (10, 100, 1000)]
ok &= check("C9a constant target speed > decaying tracking: distance grows without bound",
            dA[0] < dA[1] < dA[2] and dA[2] > 50, "d_T = " + ", ".join(f"{float(x):.2f}" for x in dA))
ok &= check("C9b summable target drift: distance -> 0 (non-increasing, reaches 0)",
            dB[0] >= dB[1] >= dB[2] and dB[0] > 0 and dB[2] == 0, "d_T = " + ", ".join(f"{float(x):.4f}" for x in dB))
ok &= check("C9c target speed = tracking rate: distance frozen at d_0",
            dC == [F(1), F(1), F(1)], "d_T = " + ", ".join(str(x) for x in dC))

# ---- C10 Statement 5(a): non-decreasing eps_t*h_t alone does NOT propagate (i) -------------
# beta=1, c*alpha=1. Round 0: eps=1/2, h=1 -> (i) holds with equality (1/2 >= 1/2).
# Round 1: eps=1/4, h=2 -> eps*h = 1/2 unchanged, but (1-eps)*c*alpha = 3/4 > 1/2 -> (i) fails.
def cond_i_raw(eps, h_t, c_t, a, b): return eps * h_t * b >= (1 - eps) * c_t * a
r0 = cond_i_raw(F(1, 2), F(1), F(1), F(1), F(1))
r1 = cond_i_raw(F(1, 4), F(2), F(1), F(1), F(1))
ok &= check("C10 equality at t=0, failure at t=1 despite constant eps*h", r0 and (not r1),
            "t=0: 1/2 >= 1/2 ; t=1: 1/2 >= 3/4 is false")
# the (1-eps)-free sufficient form eps*h*beta >= c*alpha does propagate when eps*h is non-decreasing
suff = all(F(1, 2 ** t) * (2 ** t) * F(1) >= F(1) * F(1, 2) for t in range(30))   # eps*h = 1 >= c*alpha = 1/2
ok &= check("C10 sufficient form eps*h*beta >= c*alpha propagates", suff, "eps_t*h_t = 1 >= c*alpha = 1/2 for all t")

print("\nALL PASS" if ok else "\nSOME FAIL")
