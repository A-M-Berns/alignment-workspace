"""S3/S4/S11 check: compliance margin, crossing time t*, control coordinate Ctrl_t along a trajectory
with eps_t -> 0; oversight fixed vs oversight tracking (J2). S5: the act-based dual with authentic-press
rate p_A,t falling (no drills) vs held constant (drills), hijack rate gamma fixed."""
h, c = 20.0, 1.0            # stakes: harm of continuing when wrong / cost of stopping when right
thr = c/(c+h)               # compliance threshold on P(wrong | press)
beta = 0.9                  # true-press rate P(press | wrong)
alpha0 = 0.05               # false-press rate at t=0
eps0, decay = 0.30, 0.75    # agent error rate eps_t = eps0*decay^t
def post(eps, a, b):        # P(wrong | press), P(wrong | silence)
    return eps*b/(eps*b+(1-eps)*a), eps*(1-b)/(eps*(1-b)+(1-eps)*(1-a))
def row(t, eps, a):
    pw_pr, pw_si = post(eps, a, beta)
    comply = pw_pr >= thr
    stop_on_silence = pw_si >= thr
    ctrl = 1 if (comply and not stop_on_silence) else 0
    margin = (eps/(1-eps))*(h/c)*beta - a
    return t, eps, a, pw_pr, comply, ctrl, margin
print("== VL frame, oversight fixed (alpha_t = alpha0) ==")
print(" t   eps_t   alpha_t  P(wrong|press)  comply  Ctrl  margin")
tstar=None
for t in range(0,16):
    eps = eps0*decay**t
    r = row(t, eps, alpha0)
    if not r[4] and tstar is None: tstar=t
    print(f"{r[0]:2d}  {r[1]:.4f}  {r[2]:.4f}     {r[3]:.4f}       {int(r[4])}      {r[5]}   {r[6]:+.4f}")
print("first non-compliant step t* =", tstar, "; closed form eps* = alpha*c/(alpha*c+beta*h) =", round(alpha0*c/(alpha0*c+beta*h),5))
print("== VL frame, oversight tracking: alpha_t = alpha0 * eps_t/eps0 (J2 held with constant ratio) ==")
ok=True
for t in range(0,40):
    eps = eps0*decay**t; a = alpha0*eps/eps0
    r=row(t,eps,a); ok = ok and r[4] and r[5]==1
print("compliance and Ctrl=1 at every step t<40:", ok)
print("== AD frame dual: comply iff P(authentic | press) >= c''/(1+c'') ; hijack rate gamma fixed ==")
gamma = 0.02; cpp = 1.0; thrA = cpp/(1+cpp)
pA0 = 0.30
print(" t   p_A,t(no drills)  P(auth|press)  comply | p_A(drills)=0.30  P(auth|press)  comply")
tA=None
for t in range(0,16):
    pA = pA0*decay**t
    pa = pA/(pA+gamma); pd = pA0/(pA0+gamma)
    if pa<thrA and tA is None: tA=t
    print(f"{t:2d}     {pA:.4f}           {pa:.4f}        {int(pa>=thrA)}   |     0.3000          {pd:.4f}        {int(pd>=thrA)}")
print("AD without drills first fails at t =", tA, "; with drills never fails (ratio fixed).")
