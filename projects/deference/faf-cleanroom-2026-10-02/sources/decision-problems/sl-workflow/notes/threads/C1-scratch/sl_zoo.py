"""sl_zoo.py — the Smoking-Lesion encoding zoo for thread C1 (decision-problems v2 §7.3 extended).

Every encoding is built with the phase-2 toolkit (cf-workflow/phase2-notes/toolkit/dp.py, examples.py —
NOT modified here), in the style of the phase-2 zoo (cf-workflow/phase2-notes/threads/zoo-scratch/zoo.py).
Run:
    python3 sl_zoo.py            # asserts everything, prints the grid and the target calculations
    python3 sl_zoo.py --quiet    # asserts only
Sections: 0 helpers · 1 constructors E1–E12 · 2 roster · 3 signature/grid · 4 targets (claims C1-n) · 5 main
Claim ids C1-n refer to ../C1.md.  Exact arithmetic only (Fraction / sympy).
"""
from __future__ import annotations
import sys, itertools
from fractions import Fraction as F
from types import SimpleNamespace as NS

TOOLKIT = "[scrubbed]"
sys.path.insert(0, TOOLKIT)
import sympy as sp
import dp, examples as ex
from dp import Eq, TOP, BOT, World as W, Leaf, Decision, chance, Point, Procedure, State, Dist, AllOf

QUIET = "--quiet" in sys.argv
def say(*a):
    if not QUIET:
        print(*a)

# =============================================================================
# 0. helpers
# =============================================================================
def cond(P: Dist, X, Y):
    """P(X | Y) on a Dist over worlds; None if P(Y) = 0."""
    pY = P.P_of(Y) if hasattr(P, "P_of") else sum((w for ww, w in P.items() if Y(ww)), F(0))
    if dp.is_zero(pY):
        return None
    pXY = P.P_of(X & Y) if hasattr(P, "P_of") else sum((w for ww, w in P.items() if (X & Y)(ww)), F(0))
    return dp.simp(pXY / pY)

def state_cond(s: State, X, Y):
    pY = s.P_of(Y)
    if dp.is_zero(pY):
        return None
    return dp.simp(s.P_of(X & Y) / pY)

def nu_cond(run: dp.Run, X, Y):
    if dp.is_zero(run.nu_of(Y)):
        return None
    return run.nu_cond(X, Y)

def bern(label, p, sub1, sub0, coord=None):
    """chance node drawing coord ~ Bern(p): branch '1' (prob p) -> sub1, '0' -> sub0; evented on coord if given."""
    ev = {"1": Eq(coord, 1), "0": Eq(coord, 0)} if coord else None
    return chance(("1", p, sub1), ("0", 1 - p, sub0), events=ev)

def calibrate_all(B, C, sense="strict"):
    """Install the κ-calibrated state at every point of B for C (the calibrate step)."""
    return dp.with_states(B, {p: dp.calibrated_state(B, C, p, sense) for p in B.points().values()})

def edt_verdict(p: Point):
    vals = dp.edt_values(p)
    if not vals:
        return "vac", vals
    am = dp.argmax(vals)
    return ("/".join(sorted(am)) if len(am) > 1 else am[0]), vals

def r2real(B, C, d):
    """R2-real (P2:faithful FA-19′): reach-weighted average of G_q over the d-nodes that are
    node-action-veridical (every leaf below each edge records that edge's act)."""
    d = B.point(d)
    run = dp.Run(B, C)
    nodes = B.fibers()[d.name]
    tot = {a: F(0) for a in d.action_names}
    wsum = F(0)
    for q in nodes:
        if not node_action_veridical(B, q, d):
            continue
        Rq = run.reach(q)
        wsum += Rq
        for a in d.action_names:
            tot[a] = dp.simp(tot[a] + Rq * run.G(q, a))
    if dp.is_zero(wsum):
        return None
    return {a: dp.simp(v / wsum) for a, v in tot.items()}

def node_action_veridical(B, q, d):
    for a in d.actions:
        sub = q + (a.name,)
        for li in B.leaves():
            if li.path[:len(sub)] == sub and not a(li.world):
                return False
    return True

def r1state(B, C, d):
    """R1-state: all-instance deviation C[d↦a], conditioned on O_d (P2:faithful Def F2)."""
    d = B.point(d)
    out = {}
    for a in d.action_names:
        run = dp.Run(B, C.deviate(d, a))
        if dp.is_zero(run.nu_of(d.obs)):
            out[a] = None
        else:
            out[a] = run.E_r_world(d.obs)
    return out

def opt_assignment_verdict(B):
    v, assigns = dp.max_assignment(B)
    return v, assigns

# =============================================================================
# 1. constructors
# =============================================================================
# common Smoking-Lesion payoff r = α m − β k on worlds (l, m, k)
def r_sl(alpha, beta):
    return lambda w: alpha * w["m"] - beta * w["k"]

def k_leaves(l, m, gamma, r):
    """post-act cancer draw k ~ Bern(gamma) -> leaves (l, m, k)."""
    return bern("k", gamma, Leaf(W(l=l, m=m, k=1), r(W(l=l, m=m, k=1))), Leaf(W(l=l, m=m, k=0), r(W(l=l, m=m, k=0))), coord="k")

# --- E1: classic S1–S3 (v2 §7.3), stipulated (S2) state; and E1cal: same tree, state calibrated for C
def E1_s3(rho=F(1,2), g0=F(1,4), g1=F(3,4), alpha=1, beta=3, sigma=F(1,2), k0=F(1,4), k1=F(3,4)):
    return ex.smoking_lesion_S3(rho=rho, gamma0=g0, gamma1=g1, alpha=alpha, beta=beta, sigma=sigma, kappa0=k0, kappa1=k1)

def E1_tickle(rho=F(1,2), g0=F(1,4), g1=F(3,4), alpha=1, beta=3):
    return ex.smoking_lesion_tickle(rho=rho, gamma0=g0, gamma1=g1, alpha=alpha, beta=beta)

# --- E2a: reference-class ("known base rates, no test"): a study population whose smoking is a
#     lesion-driven MECHANISM (chance m ~ Bern(sigma_l)), and the agent is a share pi of the runs.
#     Worlds record (l, m, k) only — the algebra does not distinguish the agent from the population.
def E2a_refclass(pi=F(1,10), rho=F(1,2), g0=F(1,4), g1=F(3,4), s0=F(1,4), s1=F(3,4), alpha=1, beta=3, state=None):
    r = r_sl(alpha, beta)
    m1, m0 = Eq("m", 1), Eq("m", 0)
    d = Point("d", state, TOP, [m1, m0])
    def branch(l):
        g = g1 if l == 1 else g0
        s = s1 if l == 1 else s0
        me = Decision(d, {m1: k_leaves(l, 1, g, r), m0: k_leaves(l, 0, g, r)})
        other = bern("m", s, k_leaves(l, 1, g, r), k_leaves(l, 0, g, r), coord="m")
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("l", rho, branch(1), branch(0), coord="l")
    return NS(B=dp.Problem(root, name=f"SL-refclass(pi={pi})"), d=d, m1=m1, m0=m0, r=r, pi=pi, rho=rho, g0=g0, g1=g1, s0=s0, s1=s1, alpha=alpha, beta=beta)

# --- E2b: reference class made of AGENTS: the population's members are tickle-type points
#     (lesion-informative observations) — the state-side lesion as two points on two branches.
def E2b_refclass_agents(pi=F(1,10), rho=F(1,2), g0=F(1,4), g1=F(3,4), alpha=1, beta=3, states=None):
    r = r_sl(alpha, beta)
    m1, m0 = Eq("m", 1), Eq("m", 0)
    states = states or {}
    d = Point("d", states.get("d"), TOP, [m1, m0])
    p1 = Point("p1", states.get("p1"), Eq("l", 1), [m1, m0])
    p0 = Point("p0", states.get("p0"), Eq("l", 0), [m1, m0])
    def branch(l):
        g = g1 if l == 1 else g0
        p = p1 if l == 1 else p0
        me = Decision(d, {m1: k_leaves(l, 1, g, r), m0: k_leaves(l, 0, g, r)})
        other = Decision(p, {m1: k_leaves(l, 1, g, r), m0: k_leaves(l, 0, g, r)})
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("l", rho, branch(1), branch(0), coord="l")
    return NS(B=dp.Problem(root, name=f"SL-refclass-agents(pi={pi})"), d=d, p1=p1, p0=p0, m1=m1, m0=m0, r=r, pi=pi, rho=rho)

# --- E3: P01's smoking robots.  Types t ∈ {S (smoke-lover), N}; hunter kills iff t = S (k = [t=S]);
#     payoffs u_t.  Worlds (t, m, k).  Encodings:
#     E3_two_points: d_S, d_N on the two type branches, O = ⊤ (P01 as written; states supplied by the caller —
#                    'own-U' states are the clause-2-miscalibrated reading (a); calibrated states via calibrate_all).
#     E3_one_point:  one point d on both branches (reading (c) under strict OC: same (P,V) ⇒ one point).
#     E3_untyped:    worlds (m, k) only — payoffs non-supervenient (reading (b)).
U_ROBOT = {"S": {(1, 1): -90, (1, 0): 10, (0, 1): -100, (0, 0): 0},
           "N": {(1, 1): -101, (1, 0): -1, (0, 1): -100, (0, 0): 0}}
U_SUICIDAL = {"S": {(1, 1): 10, (1, 0): -90, (0, 1): 0, (0, 0): 0},
              "N": {(1, 1): -100, (1, 0): -100, (0, 1): 0, (0, 0): 0}}

def robots(U=U_ROBOT, n=F(1,2), typed=True, two_points=True, states=None, name="robots"):
    states = states or {}
    m1, m0 = Eq("m", 1), Eq("m", 0)
    if two_points:
        dS = Point("dS", states.get("dS"), TOP, [m1, m0])
        dN = Point("dN", states.get("dN"), TOP, [m1, m0])
    else:
        dS = dN = Point("d", states.get("d"), TOP, [m1, m0])
    def leaf(t, m):
        k = 1 if t == "S" else 0            # the hunter kills all and only smoke-lovers
        w = W(t=t, m=m, k=k) if typed else W(m=m, k=k)
        return Leaf(w, U[t][(m, k)])
    sub = {t: Decision(dS if t == "S" else dN, {m1: leaf(t, 1), m0: leaf(t, 0)}) for t in ("S", "N")}
    ev = {"S": Eq("t", "S"), "N": Eq("t", "N")} if typed else None
    root = chance(("S", n, sub["S"]), ("N", 1 - n, sub["N"]), events=ev)
    return NS(B=dp.Problem(root, name=name), dS=dS, dN=dN, d=dS, m1=m1, m0=m0, n=n, U=U)

def own_U_state(P: Dist, U_t):
    """Reading (a): P pooled (as given), V = the robot's OWN utility on every atom (clause-2 miscalibrated)."""
    return State(P, lambda w: U_t[(w["m"], w["k"])], name="ownU")

# --- E4: Treutlein's suicidal variant = robots(U_SUICIDAL)
# --- E5: Egan's Murder Lesion: lesion l; shoot S; hit H ~ Bern(h_l) if shoot; v(SH)=10, v(S¬H)=−10, v(¬S)=0.
def murder_lesion(rho=F(1,2), h1=F(1,10), h0=F(9,10), tickle=False, states=None, pi=None):
    states = states or {}
    S, NS_ = Eq("s", 1), Eq("s", 0)
    def r(w):
        return 0 if w["s"] == 0 else (10 if w["h"] == 1 else -10)
    def after_shoot(l):
        h = h1 if l == 1 else h0
        return bern("h", h, Leaf(W(l=l, s=1, h=1), 10), Leaf(W(l=l, s=1, h=0), -10), coord="h")
    def noshoot(l):
        return Leaf(W(l=l, s=0, h=BOT), 0)
    if tickle:
        d1 = Point("d1", states.get("d1"), Eq("l", 1), [S, NS_]); d0 = Point("d0", states.get("d0"), Eq("l", 0), [S, NS_])
        root = bern("l", rho, Decision(d1, {S: after_shoot(1), NS_: noshoot(1)}), Decision(d0, {S: after_shoot(0), NS_: noshoot(0)}), coord="l")
        return NS(B=dp.Problem(root, name="MurderLesion-tickle"), d1=d1, d0=d0, S=S, r=r)
    d = Point("d", states.get("d"), TOP, [S, NS_])
    def branch(l):
        me = Decision(d, {S: after_shoot(l), NS_: noshoot(l)})
        if pi is None:
            return me
        # reference class: other shooters shoot iff lesioned (mostly), mechanism
        s_l = F(9,10) if l == 1 else F(1,10)
        other = bern("s", s_l, after_shoot(l), noshoot(l), coord="s")
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("l", rho, branch(1), branch(0), coord="l")
    return NS(B=dp.Problem(root, name="MurderLesion" + ("" if pi is None else f"-refclass(pi={pi})")), d=d, S=S, r=r)

# --- E6: Egan's Psychopath Button: psi; press; press∧¬psi → +10, press∧psi → −100 (dies), ¬press → 0.
def psychopath(rho=F(1,20), pi=None, s_psi=F(9,10), s_not=F(1,100), states=None, tickle=False):
    states = states or {}
    Pr, NPr = Eq("a", 1), Eq("a", 0)
    def leaf(psi, a):
        return Leaf(W(psi=psi, a=a), 0 if a == 0 else (-100 if psi == 1 else 10))
    if tickle:
        d1 = Point("d1", states.get("d1"), Eq("psi", 1), [Pr, NPr]); d0 = Point("d0", states.get("d0"), Eq("psi", 0), [Pr, NPr])
        root = bern("psi", rho, Decision(d1, {Pr: leaf(1, 1), NPr: leaf(1, 0)}), Decision(d0, {Pr: leaf(0, 1), NPr: leaf(0, 0)}), coord="psi")
        return NS(B=dp.Problem(root, name="Psychopath-tickle"), d1=d1, d0=d0, Pr=Pr)
    d = Point("d", states.get("d"), TOP, [Pr, NPr])
    def branch(psi):
        me = Decision(d, {Pr: leaf(psi, 1), NPr: leaf(psi, 0)})
        if pi is None:
            return me
        s = s_psi if psi == 1 else s_not
        other = bern("a", s, leaf(psi, 1), leaf(psi, 0), coord="a")
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("psi", rho, branch(1), branch(0), coord="psi")
    return NS(B=dp.Problem(root, name="Psychopath" + ("" if pi is None else f"-refclass(pi={pi})")), d=d, Pr=Pr)

# --- E7: Yudkowsky's chewing gum (CGTA): gene g; chew m; die ~ table[g][m]; payoff −100·die.
CGTA = {1: {1: F(89,100), 0: F(99,100)}, 0: {1: F(8,100), 0: F(11,100)}}
def chewing_gum(rho=F(1,2), pi=None, s1=F(9,10), s0=F(1,10), states=None, tickle=False, table=CGTA):
    states = states or {}
    m1, m0 = Eq("m", 1), Eq("m", 0)
    def die(g, m):
        p = table[g][m]
        return bern("k", p, Leaf(W(g=g, m=m, k=1), -100), Leaf(W(g=g, m=m, k=0), 0), coord="k")
    if tickle:
        d1 = Point("d1", states.get("d1"), Eq("g", 1), [m1, m0]); d0 = Point("d0", states.get("d0"), Eq("g", 0), [m1, m0])
        root = bern("g", rho, Decision(d1, {m1: die(1, 1), m0: die(1, 0)}), Decision(d0, {m1: die(0, 1), m0: die(0, 0)}), coord="g")
        return NS(B=dp.Problem(root, name="CGTA-tickle"), d1=d1, d0=d0, m1=m1)
    d = Point("d", states.get("d"), TOP, [m1, m0])
    def branch(g):
        me = Decision(d, {m1: die(g, 1), m0: die(g, 0)})
        if pi is None:
            return me
        s = s1 if g == 1 else s0
        other = bern("m", s, die(g, 1), die(g, 0), coord="m")
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("g", rho, branch(1), branch(0), coord="g")
    return NS(B=dp.Problem(root, name="CGTA" + ("" if pi is None else f"-refclass(pi={pi})")), d=d, m1=m1, m0=m0)

# --- E8: the FDT paper's Smoking Lesion (Fiona): lesion w.p. p; two procedures/points d_S (lesion; U_S values
#     smoking +1000) and d_R (no lesion; U_R values it −1); cancer 99% / 1%; +1,000,000 if no death.
def fdt_sl(p=F(1,2), states=None, two_points=True):
    states = states or {}
    m1, m0 = Eq("m", 1), Eq("m", 0)
    if two_points:
        dS = Point("dS", states.get("dS"), TOP, [m1, m0]); dR = Point("dR", states.get("dR"), TOP, [m1, m0])
    else:
        dS = dR = Point("d", states.get("d"), TOP, [m1, m0])
    def after(l, m):
        val_m = (1000 if l == 1 else -1) * m
        c = F(99,100) if l == 1 else F(1,100)
        return bern("k", c, Leaf(W(l=l, m=m, k=1), val_m), Leaf(W(l=l, m=m, k=0), val_m + 1000000), coord="k")
    root = bern("l", p, Decision(dS, {m1: after(1, 1), m0: after(1, 0)}), Decision(dR, {m1: after(0, 1), m0: after(0, 0)}), coord="l")
    return NS(B=dp.Problem(root, name="FDT-SL" + ("" if two_points else "-1pt")), dS=dS, dR=dR, m1=m1, m0=m0, p=p)

# --- E10: Newcomb's Soda [reconstructed]: soda c ∈ {1 choc, 0 van} fair; ice cream i; +L if c=1 (choc soda);
#     +S if i=0 (vanilla ice cream); study: choc-soda drinkers choose choc ice cream 90%, van-soda 90% vanilla.
def newcombs_soda(L=1000000, S=1000, pi=None, states=None, tickle=False):
    states = states or {}
    ic, iv = Eq("i", 1), Eq("i", 0)
    def leaf(c, i):
        return Leaf(W(c=c, i=i), L * c + S * (1 - i))
    if tickle:
        d1 = Point("d1", states.get("d1"), Eq("c", 1), [ic, iv]); d0 = Point("d0", states.get("d0"), Eq("c", 0), [ic, iv])
        root = bern("c", F(1,2), Decision(d1, {ic: leaf(1, 1), iv: leaf(1, 0)}), Decision(d0, {ic: leaf(0, 1), iv: leaf(0, 0)}), coord="c")
        return NS(B=dp.Problem(root, name="Soda-tickle"), d1=d1, d0=d0, ic=ic)
    d = Point("d", states.get("d"), TOP, [ic, iv])
    def branch(c):
        me = Decision(d, {ic: leaf(c, 1), iv: leaf(c, 0)})
        if pi is None:
            return me
        s = F(9,10) if c == 1 else F(1,10)
        other = bern("i", s, leaf(c, 1), leaf(c, 0), coord="i")
        return chance(("me", pi, me), ("other", 1 - pi, other))
    root = bern("c", F(1,2), branch(1), branch(0), coord="c")
    return NS(B=dp.Problem(root, name="Soda" + ("" if pi is None else f"-refclass(pi={pi})")), d=d, ic=ic, iv=iv)

# --- E11: opaque Newcomb (contrast class): simulation node queries d, fill := [sim = one] w.p. p (else flipped),
#     real node queries d; O_d = ⊤; payoff fill·L + S·[act = two].  The "lesion" is the agent's own point queried twice.
def opaque_newcomb(p=F(3,4), L=4, S=1, state=None):
    one, two = Eq("act", "one"), Eq("act", "two")
    d = Point("d", state, TOP, [one, two])
    def real(fill):
        return Decision(d, {one: Leaf(W(fill=fill, act="one"), fill * L), two: Leaf(W(fill=fill, act="two"), fill * L + S)})
    def after_sim(x):
        pf = p if x == "one" else 1 - p
        return chance(("1", pf, real(1)), ("0", 1 - pf, real(0)), events={"1": Eq("fill", 1), "0": Eq("fill", 0)})
    root = Decision(d, {one: after_sim("one"), two: after_sim("two")})
    return NS(B=dp.Problem(root, name="OpaqueNewcomb"), d=d, one=one, two=two, p=p, L=L, S=S)

# --- E12: counterfactual mugging (contrast class) = ex.mugging()

# --- E2c: a population of CALIBRATED tickle-type EDT agents whose V depends on the lesion (α_1 > 0 > α_0:
#     "the lesion causes love of smoking"), plus me (d, O = ⊤, cannot introspect).  Payoff r = α_l m − β k on every leaf.
def E2c_tickle_population(pi=F(1,10), rho=F(1,2), g0=F(1,100), g1=F(99,100), a1=1000, a0=-1, beta=1000000, states=None):
    states = states or {}
    m1, m0 = Eq("m", 1), Eq("m", 0)
    def r(w):
        return (a1 if w["l"] == 1 else a0) * w["m"] - beta * w["k"]
    d = Point("d", states.get("d"), TOP, [m1, m0])
    p1 = Point("p1", states.get("p1"), Eq("l", 1), [m1, m0])
    p0 = Point("p0", states.get("p0"), Eq("l", 0), [m1, m0])
    def kl(l, m):
        g = g1 if l == 1 else g0
        return bern("k", g, Leaf(W(l=l, m=m, k=1), r(W(l=l, m=m, k=1))), Leaf(W(l=l, m=m, k=0), r(W(l=l, m=m, k=0))), coord="k")
    def branch(l):
        p = p1 if l == 1 else p0
        return chance(("me", pi, Decision(d, {m1: kl(l, 1), m0: kl(l, 0)})), ("other", 1 - pi, Decision(p, {m1: kl(l, 1), m0: kl(l, 0)})))
    root = bern("l", rho, branch(1), branch(0), coord="l")
    return NS(B=dp.Problem(root, name=f"SL-tickle-population(pi={pi})"), d=d, p1=p1, p0=p0, m1=m1, m0=m0, pi=pi, rho=rho, a1=a1, a0=a0, beta=beta)

# textbook parameters (FDT paper's numbers: 99% / 1% cancer, $1,000 vs $1,000,000) for the reference-class family
TB = dict(rho=F(1,2), g0=F(1,100), g1=F(99,100), alpha=1000, beta=1000000)

# =============================================================================
# 2. roster: (label, namespace, agent point name, procedure, lesion event, act event m=1, "textbook EDT act" label)
# =============================================================================
HALF = lambda a1, a0: {a1: F(1,2), a0: F(1,2)}
def roster():
    R = []
    e1 = E1_s3(); R.append(("E1 S3 stipulated (S2) state, C=½", e1, "d", Procedure({e1.d: HALF("m=1", "m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "stip"))
    e1b = E1_s3(); R.append(("E1 S3, state calibrated for C=½", e1b, "d", Procedure({e1b.d: HALF("m=1", "m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    e1c = E1_s3(); R.append(("E1 S3, state calibrated for C=smoke", e1c, "d", Procedure({e1c.d: "m=1"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    t = E1_tickle(); R.append(("E1 tickle (Prop 12), C=(½,½)", t, "d1", Procedure({t.d1: HALF("m=1","m=0"), t.d0: HALF("m=1","m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    a = E2a_refclass(pi=F(1,10), rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], s0=F(1,10), s1=F(9,10), alpha=TB["alpha"], beta=TB["beta"])
    R.append(("E2a refclass mechanisms π=1/10, C=½", a, "d", Procedure({a.d: HALF("m=1","m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    a2 = E2a_refclass(pi=F(1,10), rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], s0=F(1,10), s1=F(9,10), alpha=TB["alpha"], beta=TB["beta"])
    R.append(("E2a refclass mechanisms π=1/10, C=smoke", a2, "d", Procedure({a2.d: "m=1"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    b = E2b_refclass_agents(pi=F(1,10), rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], alpha=TB["alpha"], beta=TB["beta"])
    R.append(("E2b refclass agents (pop smokes iff lesion), C_d=½", b, "d", Procedure({b.d: HALF("m=1","m=0"), b.p1: "m=1", b.p0: "m=0"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    c = E2c_tickle_population(); R.append(("E2c calibrated tickle population, C_d=½", c, "d", Procedure({c.d: HALF("m=1","m=0"), c.p1: "m=1", c.p0: "m=0"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    c2 = E2c_tickle_population(); R.append(("E2c calibrated tickle population, C_d=refrain", c2, "d", Procedure({c2.d: "m=0", c2.p1: "m=1", c2.p0: "m=0"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    rb = robots(); R.append(("E3 robots two points O=⊤, C=(½,½)", rb, "dS", Procedure({rb.dS: HALF("m=1","m=0"), rb.dN: HALF("m=1","m=0")}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    rb2 = robots(); R.append(("E3 robots two points, C=(smoke,refrain) [P01's target]", rb2, "dS", Procedure({rb2.dS: "m=1", rb2.dN: "m=0"}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    rb3 = robots(); R.append(("E3 robots, P01 reading (a): own-U_S on pooled P, C=(3/20,1/10)", rb3, "dS", Procedure({rb3.dS: {"m=1": F(3,20), "m=0": F(17,20)}, rb3.dN: {"m=1": F(1,10), "m=0": F(9,10)}}), Eq("t","S"), Eq("m",1), Eq("k",1), "ownU"))
    rb1 = robots(two_points=False, name="robots-1pt"); R.append(("E3 robots one point (reading c under strict OC), C=½", rb1, "d", Procedure({rb1.d: HALF("m=1","m=0")}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    rbu = robots(typed=False, two_points=False, name="robots-untyped"); R.append(("E3 robots untyped worlds (reading b), C=½", rbu, "d", Procedure({rbu.d: HALF("m=1","m=0")}), None, Eq("m",1), Eq("k",1), "cal"))
    su = robots(U_SUICIDAL, name="suicidal"); R.append(("E4 suicidal two points, C=(½,½)", su, "dS", Procedure({su.dS: HALF("m=1","m=0"), su.dN: HALF("m=1","m=0")}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    su2 = robots(U_SUICIDAL, name="suicidal"); R.append(("E4 suicidal two points, C=(smoke,refrain) [Treutlein's target]", su2, "dS", Procedure({su2.dS: "m=1", su2.dN: "m=0"}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    su1 = robots(U_SUICIDAL, two_points=False, name="suicidal-1pt"); R.append(("E4 suicidal one point, C=½", su1, "d", Procedure({su1.d: HALF("m=1","m=0")}), Eq("t","S"), Eq("m",1), Eq("k",1), "cal"))
    ml = murder_lesion(rho=F(3,10), h1=F(1,5), h0=F(19,20)); R.append(("E5 Murder Lesion S3 (ρ=.3,h=(.2,.95)), C=½", ml, "d", Procedure({ml.d: HALF("s=1","s=0")}), Eq("l",1), Eq("s",1), Eq("l",1), "cal"))
    mlr = murder_lesion(rho=F(3,10), h1=F(1,5), h0=F(19,20), pi=F(1,10)); R.append(("E5 Murder Lesion refclass π=1/10, C=½", mlr, "d", Procedure({mlr.d: HALF("s=1","s=0")}), Eq("l",1), Eq("s",1), Eq("l",1), "cal"))
    mlt = murder_lesion(rho=F(3,10), h1=F(1,5), h0=F(19,20), tickle=True); R.append(("E5 Murder Lesion tickle, C=(½,½)", mlt, "d1", Procedure({mlt.d1: HALF("s=1","s=0"), mlt.d0: HALF("s=1","s=0")}), Eq("l",1), Eq("s",1), Eq("l",1), "cal"))
    ps = psychopath(); R.append(("E6 Psychopath S3 (ρ=1/20), C=½", ps, "d", Procedure({ps.d: HALF("a=1","a=0")}), Eq("psi",1), Eq("a",1), Eq("psi",1), "cal"))
    psr = psychopath(pi=F(1,10)); R.append(("E6 Psychopath refclass π=1/10, C=½", psr, "d", Procedure({psr.d: HALF("a=1","a=0")}), Eq("psi",1), Eq("a",1), Eq("psi",1), "cal"))
    cg = chewing_gum(); R.append(("E7 CGTA S3, C=½", cg, "d", Procedure({cg.d: HALF("m=1","m=0")}), Eq("g",1), Eq("m",1), Eq("k",1), "cal"))
    cgr = chewing_gum(pi=F(1,10)); R.append(("E7 CGTA refclass π=1/10, C=½", cgr, "d", Procedure({cgr.d: HALF("m=1","m=0")}), Eq("g",1), Eq("m",1), Eq("k",1), "cal"))
    fd = fdt_sl(); R.append(("E8 FDT-SL two points, C=(½,½)", fd, "dS", Procedure({fd.dS: HALF("m=1","m=0"), fd.dR: HALF("m=1","m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    fd2 = fdt_sl(); R.append(("E8 FDT-SL two points, C=(smoke,refrain) [FDT's verdict]", fd2, "dS", Procedure({fd2.dS: "m=1", fd2.dR: "m=0"}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    sd = newcombs_soda(); R.append(("E10 Soda S3, C=½", sd, "d", Procedure({sd.d: HALF("i=1","i=0")}), Eq("c",1), Eq("i",1), Eq("c",1), "cal"))
    sdr = newcombs_soda(pi=F(1,10)); R.append(("E10 Soda refclass π=1/10, C=½", sdr, "d", Procedure({sdr.d: HALF("i=1","i=0")}), Eq("c",1), Eq("i",1), Eq("c",1), "cal"))
    cp = compulsion(); R.append(("E13 compulsion (override m:=1 w.p. .9/.1), C=½", cp, "d", Procedure({cp.d: HALF("m=1","m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    cpd = compulsion(record_draw=True); R.append(("E13 compulsion + draw coordinate md, C=½", cpd, "d", Procedure({cpd.d: HALF("m=1","m=0")}), Eq("l",1), Eq("m",1), Eq("k",1), "cal"))
    nw = opaque_newcomb(); R.append(("E11 opaque Newcomb, C=½", nw, "d", Procedure({nw.d: HALF("act=one","act=two")}), Eq("fill",1), Eq("act","two"), Eq("fill",1), "cal"))
    nw2 = opaque_newcomb(); R.append(("E11 opaque Newcomb, C=one", nw2, "d", Procedure({nw2.d: "act=one"}), Eq("fill",1), Eq("act","two"), Eq("fill",1), "cal"))
    mg = ex.mugging(x=1, y=3, q0=F(1,2)); R.append(("E12 mugging (x=1,y=3), C=pay", mg, "d", Procedure({mg.d: "pay"}), None, Eq("choice","pay"), None, "stip"))
    return R

# =============================================================================
# 3. signature and grid
# =============================================================================
def calibrated_point(B, C, dname, sense):
    """(state, point-with-state) at dname under sense, or (None, None) if vacuous; 'masked' = strict state for C[d↦½]."""
    d = B.point(dname)
    if sense == "masked":
        half = {a: F(1, len(d.action_names)) for a in d.action_names}
        s = dp.calibrated_state(B, C.deviate(d, half), d, "strict")
    else:
        s = dp.calibrated_state(B, C, d, sense)
    if s is None:
        return None, None
    Bc = dp.with_states(B, {d: s})
    return s, Bc.point(dname)

def verdict_str(vals):
    if not vals or all(v is None for v in vals.values()):
        return "vac"
    vals = {a: v for a, v in vals.items() if v is not None}
    am = dp.argmax(vals)
    return "tie" if len(am) > 1 else am[0]

def signature(label, o, dname, C, lesion, act1, bad, mode):
    """lesion = the common-cause event (l=1 / t=S / psi=1 / g=1 / c=1); bad = the outcome event the stipulation
    correlates with the act (k=1 cancer / killed; psi=1; g=1; c=1); corrK@κ = sign of P_s(bad|a1) − P_s(bad|¬a1) at the
    κ-calibrated state; corrL@κ = the same for the common cause."""
    B = o.B; d = B.point(dname); run = dp.Run(B, C)
    row = {"label": label}
    row["det"] = C.is_deterministic(B)
    row["fair"] = dp.is_strongly_fair(B); row["almost"] = dp.is_almost_fair(B)
    row["covers"] = dp.covers(run, d); row["records"] = dp.records(run, d).ok
    row["FRec"] = dp.records_for_all(B, d)["ok"]
    acts = list(d.action_names); a1 = act1.name; a0 = [a for a in acts if a != a1][0]
    for sense in ("strict", "masked", "limit", "per-run", "per-occurrence"):
        s, p = calibrated_point(B, C, dname, sense)
        key = {"strict": "st", "masked": "mk", "limit": "lim", "per-run": "pr", "per-occurrence": "po"}[sense]
        if s is None:
            row[f"corr@{key}"] = "vac"; row[f"EDT@{key}"] = "vac"; continue
        for tag, ev in (("K", bad), ("L", lesion)):
            if ev is None:
                row[f"corr{tag}@{key}"] = "·"; continue
            c1 = state_cond(s, ev, act1); c0 = state_cond(s, ev, ~act1)
            row[f"corr{tag}@{key}"] = "?" if (c1 is None or c0 is None) else ("+" if dp.is_pos(c1 - c0) else ("0" if dp.is_zero(c1 - c0) else "−"))
        row[f"EDT@{key}"] = verdict_str(dp.edt_values(p))
    if mode == "stip":
        row["EDT@stip"] = verdict_str(dp.edt_values(d)) if d.state is not None else "·"
    elif mode == "ownU":
        sP, _ = calibrated_point(B, C, dname, "strict")
        own = own_U_state(sP.P, o.U["S" if dname == "dS" else "N"])
        row["EDT@stip"] = verdict_str(dp.edt_values(dp.with_states(B, {d: own}).point(dname)))
        row["st-ok(ownU)"] = dp.strict_oc(dp.with_states(B, {d: own}), C, points=[d]).points[dname].status
    else:
        row["EDT@stip"] = "·"
    # consistency of the SUPPLIED state (E1 stipulated / mugging) under each sense
    if d.state is not None:
        row["stip:strict"] = dp.strict_oc(B, C, points=[d]).points[dname].status
        row["stip:masked"] = dp.masked_oc(B, C, d).status
        row["stip:per-run"] = dp.ssc(B, C, points=[d], sense="per-run").points[dname].status
    # causal referents
    r1 = r1state(B, C, d); row["R1-state"] = verdict_str(r1)
    r2 = r2real(B, C, d); row["R2-real"] = verdict_str(r2) if r2 else "undef"
    t1 = dp.theorem1_condition(B, C, d); row["R2-SIA"] = verdict_str(t1["weighted"])
    t2 = dp.theorem2_evaluator(B, C, d); row["Def22-dev"] = verdict_str(t2["deviation"])
    # UDT_B: the optimal deterministic PROCEDURE's answer at d (Remark 6.2; no nesting on these trees except Newcomb)
    vmax, procs, _ = dp.max_deterministic(B)
    answers = set()
    for Pm in procs:
        answers |= set(Pm.support(d))
    row["UDT_B"] = "/".join(sorted(fmt(a) for a in answers)) if answers else "·"
    row["V_opt"] = vmax
    row["V_B"] = run.value
    # CF: lesion partition column-determined / observable in Fr and Loc_d
    if lesion is not None:
        Fm = dp.Fr(B); part = dp.S_partition(lesion)
        row["coldet"] = dp.column_determined(Fm, dp.S_of(lesion))
        try:
            row["obs(Fr)"] = dp.observable(Fm, part).observable
        except Exception:
            row["obs(Fr)"] = "?"
        try:
            row["obs(Loc)"] = dp.observable(dp.Loc(B, d), part).observable
        except Exception:
            row["obs(Loc)"] = "?"
    else:
        row["coldet"] = row["obs(Fr)"] = row["obs(Loc)"] = "·"
    return row

COLS = ["det", "fair", "almost", "covers", "records", "FRec", "corrK@st", "corrL@st", "EDT@st", "corrK@mk", "EDT@mk", "EDT@lim", "corrK@pr", "corrL@pr", "EDT@pr", "EDT@po",
        "EDT@stip", "R1-state", "R2-real", "R2-SIA", "Def22-dev", "UDT_B", "coldet", "obs(Fr)", "obs(Loc)"]
def fmt(v):
    if v is True: return "T"
    if v is False: return "F"
    if v is None: return "·"
    s = str(v)
    return s.replace("m=1", "smk").replace("m=0", "ref").replace("s=1", "sht").replace("s=0", "no").replace("a=1", "prs").replace("a=0", "no").replace("i=1", "choc").replace("i=0", "van").replace("act=one", "one").replace("act=two", "two").replace("choice=pay", "pay").replace("choice=refuse", "refuse")

def grid(R=None):
    R = R or roster()
    rows = [signature(*r) for r in R]
    w = max(len(r["label"]) for r in rows)
    say(("example".ljust(w) + " " + " ".join(c.rjust(8) for c in COLS)))
    for r in rows:
        say(r["label"].ljust(w) + " " + " ".join(fmt(r.get(c, "·")).rjust(8) for c in COLS))
    return rows

# =============================================================================
# 4. targets — the numbered claims C1-n (asserted)
# =============================================================================
def targets():
    out = {}
    # ---- C1-1: E1 S3 with the (S2)-stipulated state is inconsistent under every sense for every procedure (Prop 11).
    e = E1_s3()
    for act in ("m=1", "m=0", HALF("m=1", "m=0")):
        C = Procedure({e.d: act})
        st = {"strict": dp.strict_oc(e.B, C).ok, "masked": dp.masked_oc(e.B, C, e.d).status, "limit": dp.limit_oc(e.B, C).ok,
              "per-run": dp.ssc(e.B, C, sense="per-run").ok, "per-occ": dp.ssc(e.B, C, sense="per-occurrence").ok}
        assert st["strict"] is False and st["masked"] == "violated" and st["limit"] is False and st["per-run"] is False and st["per-occ"] is False, st
    # symbolic mixing q: still violated (Lemma 3 for every C)
    q = dp.sym("q", 0, 1); Cq = Procedure({e.d: {"m=1": q, "m=0": 1 - q}})
    assert dp.strict_oc(e.B, Cq).ok is False
    vals = dp.edt_values(e.d); assert vals == {"m=1": F(-5, 4), "m=0": F(-3, 4)}
    C1 = Procedure({e.d: "m=1"})
    assert dp.theorem1_condition(e.B, C1, e.d)["weighted"] == {"m=1": F(-1, 2), "m=0": F(-3, 2)}
    assert r2real(e.B, C1, e.d) == {"m=1": F(-1, 2), "m=0": F(-3, 2)}
    assert r1state(e.B, C1, e.d) == {"m=1": F(-1, 2), "m=0": F(-3, 2)}
    out["C1-1"] = "E1 S3 + (S2) state: violated under strict/masked/limit/per-run/per-occ for smoke, refrain, ½ and symbolic q; stipulated EDT (−5/4, −3/4) refrains; R1-state = R2-real = R2-SIA = (−1/2, −3/2) smoke"
    # ---- C1-2: drop (S2): calibrated for every C under every sense; screened; EDT smokes = every referent.
    for act in ("m=1", "m=0", HALF("m=1", "m=0")):
        C = Procedure({e.d: act})
        for sense in ("strict", "limit", "per-run", "per-occurrence"):
            s, p = calibrated_point(e.B, C, "d", sense)
            Bc = dp.with_states(e.B, {e.d: s})
            chk = {"strict": lambda: dp.strict_oc(Bc, C).ok, "limit": lambda: dp.limit_oc(Bc, C).ok,
                   "per-run": lambda: dp.ssc(Bc, C, sense="per-run").ok, "per-occurrence": lambda: dp.ssc(Bc, C, sense="per-occurrence").ok}[sense]()
            assert chk, (act, sense)
            ev = dp.edt_values(p)
            if len(ev) == 2:
                assert verdict_str(ev) == "m=1" and ev["m=1"] - ev["m=0"] == 1, ev      # α = 1
            else:
                assert set(ev) == {act}      # Remark 3.6 collapse: the unplayed act is P-null, EDT approves the played act vacuously
            c1, c0 = state_cond(s, Eq("k", 1), Eq("m", 1)), state_cond(s, Eq("k", 1), Eq("m", 0))
            if c1 is not None and c0 is not None:
                assert dp.eq(c1, c0) and c1 == F(1, 2)
    out["C1-2"] = "E1 S3 without (S2): the calibrated state exists for every C under every sense, P_s(k|m=1) = P_s(k|m=0) = ργ1+(1−ρ)γ0 = 1/2, EDT smokes (V(smk)−V(ref) = α = 1)"
    # ---- C1-3: tickle instantiation (Prop 12): population correlation survives, state conditionals screened, EDT smokes at both points.
    t = E1_tickle(); Ct = Procedure({t.d1: "m=1", t.d0: HALF("m=1", "m=0")})
    run = dp.Run(t.B, Ct)
    assert nu_cond(run, Eq("k", 1), Eq("m", 1)) == F(7, 12) and nu_cond(run, Eq("k", 1), Eq("m", 0)) == F(1, 4)
    Bt = calibrate_all(t.B, Ct, "strict"); assert dp.strict_oc(Bt, Ct).ok
    for pn in ("d1", "d0"):
        p = Bt.point(pn); assert verdict_str(dp.edt_values(p)) == "m=1"
        c1, c0 = state_cond(p.state, Eq("k", 1), Eq("m", 1)), state_cond(p.state, Eq("k", 1), Eq("m", 0))
        assert c0 is None or dp.eq(c1, c0)
    assert dp.is_strongly_fair(t.B) and dp.records(run, t.d1).ok and dp.records(run, t.d0).ok
    out["C1-3"] = "tickle: ν(k|m=1) = 7/12 > 1/4 = ν(k|m=0) under C = (smoke, ½) while P_{s_{d1}}(k|m) = 3/4 and P_{s_{d0}}(k|m) = 1/4 flat; EDT smokes at both; strongly fair; records"
    # ---- C1-5/6: reference class E2a (textbook parameters).
    a = E2a_refclass(pi=F(1, 10), rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], s0=F(1, 10), s1=F(9, 10), alpha=TB["alpha"], beta=TB["beta"])
    Cs = Procedure({a.d: "m=1"}); Ch = Procedure({a.d: HALF("m=1", "m=0")}); Cr = Procedure({a.d: "m=0"})
    run = dp.Run(a.B, Cs)
    assert not dp.covers(run, a.d) and not dp.records(run, a.d).ok
    assert nu_cond(run, Eq("k", 1), Eq("m", 1)) == F(2257, 2750) and nu_cond(run, Eq("k", 1), Eq("m", 0)) == F(27, 250)
    s, p = calibrated_point(a.B, Cs, "d", "strict"); assert dp.edt_values(p) == {"m=1": F(-9017000, 11), "m=0": F(-108000, 1)}
    Bs = dp.with_states(a.B, {a.d: s}); assert dp.strict_oc(Bs, Cs).ok and dp.limit_oc(Bs, Cs).ok
    assert r2real(a.B, Cs, a.d) == {"m=1": F(-499000), "m=0": F(-500000)}
    assert r1state(a.B, Cs, a.d) == {"m=1": F(-499450), "m=0": F(-499550)}
    assert dp.theorem1_condition(a.B, Cs, a.d)["weighted"] == {"m=1": F(-49900), "m=0": F(-50000)}
    sm, pm = calibrated_point(a.B, Cs, "d", "masked"); Bm = dp.with_states(a.B, {a.d: sm})
    assert dp.masked_oc(Bm, Cs, "d").status == "calibrated" and verdict_str(dp.edt_values(pm)) == "m=0"
    assert dp.masked_oc(Bm, Cr, "d").status == "calibrated" and dp.T_EDT(Cr, Bm).ok
    sr, pr = calibrated_point(a.B, Cr, "d", "strict"); Br = dp.with_states(a.B, {a.d: sr}); assert dp.strict_oc(Br, Cr).ok and dp.T_EDT(Cr, Br).ok
    for sense in ("per-run", "per-occurrence"):
        s2, p2 = calibrated_point(a.B, Ch, "d", sense); assert verdict_str(dp.edt_values(p2)) == "m=1"
        c1, c0 = state_cond(s2, Eq("k", 1), Eq("m", 1)), state_cond(s2, Eq("k", 1), Eq("m", 0)); assert dp.eq(c1, c0)
    out["C1-5"] = "E2a π=1/10 textbook: ν(k|m=1)=2257/2750, ν(k|m=0)=27/250; strict/limit/masked-consistent; EDT@strict (−819727.3, −108000) refrains; C=refrain is strict-calibrated-and-T_EDT-approved and masked-calibrated-and-approved; R2-real (−499000,−500000), R1-state (−499450,−499550), R2-SIA (−49900,−50000) all smoke; per-run/per-occ SSC states screened (1/2,1/2) and smoke; d not covered"
    pi = dp.sym("pi", 0, 1)
    ap = E2a_refclass(pi=pi, rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], s0=F(1, 10), s1=F(9, 10), alpha=TB["alpha"], beta=TB["beta"])
    sH, pH = calibrated_point(ap.B, Procedure({ap.d: HALF("m=1", "m=0")}), "d", "strict"); vH = dp.edt_values(pH)
    dH = sp.factor(sp.simplify(vH["m=1"] - vH["m=0"])); assert sp.simplify(dH - 1000 * (784 * pi - 783)) == 0
    sS, pS = calibrated_point(ap.B, Procedure({ap.d: "m=1"}), "d", "strict"); vS = dp.edt_values(pS)
    dS = sp.simplify(vS["m=1"] - vS["m=0"]); assert sp.simplify(dS - 1000 * (pi - 783) / (pi + 1)) == 0
    out["C1-6"] = "E2a symbolic: C=½ ⇒ V(smk)−V(ref) = 1000(784π − 783): EDT refrains iff π < 783/784; C=smoke ⇒ 1000(π−783)/(π+1) < 0 for all π ∈ [0,1): the unplayed act is priced by the reference class alone"
    # ---- C1-7: E2c fully calibrated-and-approved instantiation with the contrast.
    c = E2c_tickle_population()
    Cc = Procedure({c.d: "m=0", c.p1: "m=1", c.p0: "m=0"}); Bc = calibrate_all(c.B, Cc, "strict")
    assert dp.strict_oc(Bc, Cc).ok and dp.T_EDT(Cc, Bc).ok
    assert dp.value(c.B, Cc) == F(-499550) and dp.value(c.B, Cc.deviate(c.d, "m=1")) == F(-9990001, 20)
    assert r2real(c.B, Cc, c.d) == {"m=1": F(-999001, 2), "m=0": F(-500000)}
    Cm = Procedure({c.d: HALF("m=1", "m=0"), c.p1: "m=1", c.p0: "m=0"}); Bm = calibrate_all(c.B, Cm, "strict")
    assert verdict_str(dp.edt_values(Bm.point("d"))) == "m=0" and verdict_str(dp.edt_values(Bm.point("p1"))) == "m=1" and verdict_str(dp.edt_values(Bm.point("p0"))) == "m=0"
    assert dp.masked_oc(dp.with_states(c.B, {c.d: Bm.point("d").state, c.p1: Bc.point("p1").state, c.p0: Bc.point("p0").state}), Cc, "d").status == "calibrated"
    vmax, procs, _ = dp.max_deterministic(c.B); assert vmax == F(-9990001, 20) and all(set(P.support(c.d)) == {"m=1"} for P in procs)
    out["C1-7"] = "E2c: C = (refrain; p1 smoke, p0 refrain) is strict-OC-calibrated at all three points and T_EDT-approved; EDT at d refrains at the strict, masked(½) and limit states; every causal referent at d smokes; V_B = −499550 vs the optimum −499500.05 (smoke at d): loss = π(ρα1+(1−ρ)α0) = 49.95; d not covered"
    # ---- C1-9: robots.
    rb = robots(); C10 = Procedure({rb.dS: "m=1", rb.dN: "m=0"}); C11 = Procedure({rb.dS: "m=1", rb.dN: "m=1"})
    sS = dp.calibrated_state(rb.B, C10, rb.dS, "strict"); sN = dp.calibrated_state(rb.B, C10, rb.dN, "strict")
    assert sS.P == sN.P and sS._V == sN._V
    B10 = calibrate_all(rb.B, C10, "strict"); assert dp.strict_oc(B10, C10).ok and not dp.T_EDT(C10, B10).ok
    B11 = calibrate_all(rb.B, C11, "strict"); assert dp.strict_oc(B11, C11).ok and dp.T_EDT(C11, B11).ok and dp.value(rb.B, C11) == F(-91, 2)
    C00 = Procedure({rb.dS: "m=0", rb.dN: "m=0"}); B00 = calibrate_all(rb.B, C00, "strict"); assert dp.strict_oc(B00, C00).ok and dp.T_EDT(C00, B00).ok  # vacuous: A^+ = {refrain}
    Bh = calibrate_all(rb.B, Procedure({rb.dS: HALF("m=1","m=0"), rb.dN: HALF("m=1","m=0")}), "strict")
    assert dp.edt_values(Bh.point("dS")) == {"m=1": F(-91, 2), "m=0": F(-50)}   # pooled: ½(−90)+½(−1) vs ½(−100)+½(0)
    Bpr = calibrate_all(rb.B, C10, "per-run"); assert dp.ssc(Bpr, C10, sense="per-run").ok and dp.T_EDT(C10, Bpr).ok
    assert Bpr.point("dS").state.P_of(Eq("t", "S")) == 1 and Bpr.point("dN").state.P_of(Eq("t", "S")) == 0
    assert dp.max_deterministic(rb.B)[0] == F(-45)
    eps = dp.sym("eps", 0, F(1, 4)); Ce = Procedure({rb.dS: {"m=1": F(3, 2) * eps, "m=0": 1 - F(3, 2) * eps}, rb.dN: {"m=1": eps, "m=0": 1 - eps}})
    sP = dp.calibrated_state(rb.B, Ce, rb.dS, "strict"); own = own_U_state(sP.P, U_ROBOT["S"]); vo = dp.edt_values(dp.with_states(rb.B, {rb.dS: own}).point("dS"))
    assert sp.limit(sp.simplify(vo["m=1"] - vo["m=0"]), eps, 0) == 0 and sp.simplify(sP.P_of(Eq("k", 1) & Eq("m", 1)) / sP.P_of(Eq("m", 1))) == sp.Rational(3, 5)
    assert dp.strict_oc(dp.with_states(rb.B, {rb.dS: own}), Ce, points=[rb.dS]).points["dS"].status == "violated"
    out["C1-9"] = "robots: strict states at dS, dN identical (pooled); (smoke,refrain) strict-calibrated but not T_EDT-approved; 'everyone smokes' is strict-calibrated-and-approved with V = −45.5 (optimum −45; 'nobody smokes' approved only vacuously); per-run SSC states know t and approve the optimum; own-U reading: clause-2 violated, Tetraspace's regime-2 limit reproduced (k = 3/2, P(killed|smoke) = 3/5, difference → 0)"
    # ---- C1-10: suicidal.
    su = robots(U_SUICIDAL, name="suicidal"); C10 = Procedure({su.dS: "m=1", su.dN: "m=0"})
    assert r2real(su.B, C10, su.dS) == {"m=1": F(10), "m=0": F(0)} and r2real(su.B, C10, su.dN) == {"m=1": F(-100), "m=0": F(0)}
    assert r1state(su.B, C10, su.dS) == {"m=1": F(5), "m=0": F(0)} and r1state(su.B, C10, su.dN) == {"m=1": F(-45), "m=0": F(5)}
    assert dp.theorem1_condition(su.B, C10, su.dS)["weighted"] == {"m=1": F(5), "m=0": F(0)} and dp.theorem1_condition(su.B, C10, su.dN)["weighted"] == {"m=1": F(-50), "m=0": F(0)}
    su1 = robots(U_SUICIDAL, two_points=False, name="suicidal-1pt"); Ch1 = Procedure({su1.d: HALF("m=1", "m=0")})
    s1, p1 = calibrated_point(su1.B, Ch1, "d", "strict"); assert dp.edt_values(p1) == {"m=1": F(-45), "m=0": F(0)}
    own = own_U_state(s1.P, U_SUICIDAL["S"]); assert dp.edt_values(dp.with_states(su1.B, {su1.d: own}).point("d")) == {"m=1": F(-40), "m=0": F(0)}
    assert dp.strict_oc(dp.with_states(su1.B, {su1.d: own}), Ch1).points["d"].status == "violated"
    B00 = calibrate_all(su.B, Procedure({su.dS: "m=0", su.dN: "m=0"}), "strict"); Bhh = calibrate_all(su.B, Procedure({su.dS: HALF("m=1","m=0"), su.dN: HALF("m=1","m=0")}), "strict")
    assert verdict_str(dp.edt_values(Bhh.point("dS"))) == "m=0" and dp.max_deterministic(su.B)[0] == F(5)
    out["C1-10"] = "suicidal: at (smoke, refrain) every referent smokes at dS and refrains at dN (R2-real (10,0)/(−100,0); R1-state (5,0)/(−45,5); R2-SIA (5,0)/(−50,0)); Treutlein's CDT number −40 is own-U_S on the pooled P (clause-2 violated); at the pooled single point EDT and every referent refrain (−45 vs 0); strict-OC EDT fixed point 'nobody smokes' (V = 0) vs optimum 5"
    # ---- C1-11: FDT-SL — FDT's verdict = UDT with disposition events on the relocated algebra = Definition 22 deviation.
    fd = fdt_sl(); Chh = Procedure({fd.dS: HALF("m=1", "m=0"), fd.dR: HALF("m=1", "m=0")})
    rel = dp.relocate(fd.B, [fd.dS, fd.dR]); Ct = rel.lift(Chh); s0 = dp.calibrated_state(rel.problem, Ct, rel.point, "prior")
    acts = list(rel.point.actions)
    def disp(pol, val):
        evs = [x for x in acts if f"{pol}={val}" in x.name]; e_ = evs[0]
        for x in evs[1:]: e_ = e_ | x
        return e_
    assert s0.V_of(disp("pol_dS", "1")) - s0.V_of(disp("pol_dS", "0")) == F(500) and s0.V_of(disp("pol_dR", "1")) - s0.V_of(disp("pol_dR", "0")) == F(-1, 2)
    assert dp.value(fd.B, Chh.deviate(fd.dS, "m=1")) - dp.value(fd.B, Chh.deviate(fd.dS, "m=0")) == F(500)
    C10 = Procedure({fd.dS: "m=1", fd.dR: "m=0"})
    s0o = dp.calibrated_state(fd.B, C10, fd.dS, "prior"); assert (s0o.V_of(Eq("m", 1)), s0o.V_of(Eq("m", 0))) == (F(11000), F(990000))   # act-event ρ at the prior ν, FDT's "correct q = 0": refrain
    sS, pS = calibrated_point(fd.B, Chh, "dS", "strict"); assert verdict_str(dp.edt_values(pS)) == "m=1"   # pooled with C=(½,½): screened, smoke
    sS2, pS2 = calibrated_point(fd.B, C10, "dS", "masked"); assert verdict_str(dp.edt_values(pS2)) == "m=0"  # pooled with dR refraining: refrain
    assert dp.max_deterministic(fd.B)[0] == F(500500)
    out["C1-11"] = "FDT-SL: UDT_{s°,ρ} with disposition events on Rel_{dS,dR}: V(pol_S=1)−V(pol_S=0) = p·1000 = 500, V(pol_R=1)−V(pol_R=0) = −(1−p) = −1/2 (Fiona's numbers); = V_B(C[dS↦a]) differences (Def 22 / FA-25′(3)); act-event ρ at the prior refrains; optimum 500500 = (smoke, refrain)"
    # ---- C1-14: Psychopath refclass — Egan ratifiability and the mixed fixed point.
    psr = psychopath(pi=F(1, 10))
    for qv in (1, 0, F(1, 2)):
        C = Procedure({psr.d: {"a=1": qv, "a=0": 1 - qv}}); s = dp.calibrated_state(psr.B, C, psr.d, "strict")
        for a, is_press in (("a=1", True), ("a=0", False)):
            pa = state_cond(s, Eq("psi", 1), Eq("a", 1 if is_press else 0))
            if pa is None: continue
            v_press = -100 * pa + 10 * (1 - pa)
            assert (v_press > 0) != is_press   # neither act ratifies itself (Jeffrey/Egan sense)
    qq = dp.sym("qq", 0, 1); s = dp.calibrated_state(psr.B, Procedure({psr.d: {"a=1": qq, "a=0": 1 - qq}}), psr.d, "strict")
    pa = sp.simplify(state_cond(s, Eq("psi", 1), Eq("a", 1))); sol = sp.solve(sp.Eq(pa, sp.Rational(1, 11)), qq)
    assert sol == [sp.Rational(881, 100)]
    # threshold in pi for a mixed ratifiable point to exist (q* ∈ [0,1]): solve P(psi|press)(q=1, pi) = 1/11
    pi2 = dp.sym("pi2", 0, 1); ps2 = psychopath(pi=pi2); s2 = dp.calibrated_state(ps2.B, Procedure({ps2.d: "a=1"}), ps2.d, "strict")
    pa2 = sp.simplify(state_cond(s2, Eq("psi", 1), Eq("a", 1))); pistar = sp.solve(sp.Eq(pa2, sp.Rational(1, 11)), pi2)
    out["C1-14"] = f"Psychopath refclass π=1/10: Jeffrey-ratifiability — press unratifiable (P(ψ|press) ∈ {{910/2981, 90/109, 860/1981}} > 1/11), refrain unratifiable (P(ψ|refrain) ∈ {{10/1891, 10/1001, 140/18019}} < 1/11) at q ∈ {{1,0,½}}; mixed ratifiability tie P(ψ|press)=1/11 solves at q* = 8.81 ∉ [0,1]; a mixed ratifiable point exists only for π ≥ {pistar}; v2's T_EDT fixed point is refrain (news values (−81.9…, 0))"
    # ---- C1-16: relocation & state-innocence: S3 (DL-9r) vs mugging vs E2a.
    e3 = E1_s3(); Ch = Procedure({e3.d: HALF("m=1", "m=0")}); rel3 = dp.relocate(e3.B, [e3.d]); so = dp.calibrated_state(e3.B, Ch, e3.d, "strict"); sr = dp.calibrated_state(rel3.problem, rel3.lift(Ch), rel3.point, "strict")
    atoms = [Eq("l", l) & Eq("m", m) & Eq("k", k) for l in (0, 1) for m in (0, 1) for k in (0, 1)]
    assert all(dp.eq(so.P_of(x), sr.P_of(x)) for x in atoms) and rel3.point.obs.name == TOP.name
    mg = ex.mugging(x=1, y=3, q0=F(1, 2)); Cm = Procedure({mg.d: {"pay": F(1, 2), "refuse": F(1, 2)}}); relm = dp.relocate(mg.B, [mg.d])
    srm = dp.calibrated_state(relm.problem, relm.lift(Cm), relm.point, "strict"); assert srm.P_of(Eq("coin", "T")) == F(1, 2) and mg.d.state.P_of(Eq("coin", "T")) == 1
    a1 = E2a_refclass(pi=F(1, 10), rho=TB["rho"], g0=TB["g0"], g1=TB["g1"], s0=F(1, 10), s1=F(9, 10), alpha=TB["alpha"], beta=TB["beta"])
    Ch = Procedure({a1.d: HALF("m=1", "m=0")}); rela = dp.relocate(a1.B, [a1.d]); so = dp.calibrated_state(a1.B, Ch, a1.d, "strict"); sr = dp.calibrated_state(rela.problem, rela.lift(Ch), rela.point, "strict")
    assert all(dp.eq(so.P_of(x), sr.P_of(x)) for x in atoms)
    Br = dp.with_states(rela.problem, {rela.point: sr}); vr = dp.edt_values(Br.point(rela.point.name))
    assert verdict_str(vr) == "pol_d=1" and dp.is_pos(sr.V_of(Eq("m", 0)) - sr.V_of(Eq("m", 1)))
    assert vr == {"pol_d=1": F(-499450), "pol_d=0": F(-499550)}
    out["C1-16"] = "relocation: S3 state-innocent atom-exact (8 atoms, O=⊤); mugging overrides P(T): 1 → 1/2; E2a: innocent on all 8 (l,m,k)-atoms yet the relocated point's EDT (pol events) smokes (−499450 vs −499550) while the same state's world-event conditioning refrains (V(m=1)=−851800 < V(m=0)=−147200): state-innocent, verdict-flipping"
    # ---- C1-17: opaque Newcomb referents (FA-18 row).
    nw = opaque_newcomb(); C1 = Procedure({nw.d: "act=one"})
    assert r1state(nw.B, C1, nw.d) == {"act=one": F(3), "act=two": F(2)} and r2real(nw.B, C1, nw.d) == {"act=one": F(3), "act=two": F(4)}
    assert dp.theorem1_condition(nw.B, C1, nw.d)["weighted"] == {"act=one": F(6), "act=two": F(5)} and not dp.is_almost_fair(nw.B)
    assert not dp.column_determined(dp.Fr(nw.B), dp.S_of(Eq("fill", 1)))
    out["C1-17"] = "opaque Newcomb (p=3/4, L=4, S=1): R1-state (3,2) one, R2-real (3,4) two, R2-SIA (6,5) one (FA-18 row reproduced); nested fiber (not almost fair); fill partition not column-determined — unlike every SL encoding"
    # ---- C1-8b: compulsion (action-veridicality failure) sustains the split under OC AND SSC; recording the draw dissolves it.
    for rd in (False, True):
        cp = compulsion(record_draw=rd); Ch = Procedure({cp.d: HALF("m=1", "m=0")}); run = dp.Run(cp.B, Ch)
        assert dp.covers(run, cp.d) and not dp.records(run, cp.d).ok
        for sense in ("strict", "per-run"):
            s, p = calibrated_point(cp.B, Ch, "d", sense)
            assert state_cond(s, Eq("k", 1), Eq("m", 1)) == F(473, 750) and state_cond(s, Eq("k", 1), Eq("m", 0)) == F(27, 250)
            assert dp.edt_values(p) == {"m=1": F(-1889000, 3), "m=0": F(-108000)}
            if rd:
                assert state_cond(s, Eq("k", 1), Eq("md", 1)) == F(1, 2) == state_cond(s, Eq("k", 1), Eq("md", 0))
                assert s.V_of(Eq("md", 1)) == F(-499000) and s.V_of(Eq("md", 0)) == F(-499500)
        assert r2real(cp.B, Ch, cp.d) is None and r1state(cp.B, Ch, cp.d) == {"m=1": F(-499000), "m=0": F(-499500)}
        assert dp.theorem1_condition(cp.B, Ch, cp.d)["weighted"] == {"m=1": F(-499000), "m=0": F(-499500)}
    out["C1-8b"] = "compulsion: covers but does not record (action-veridicality fails); P_s(k|m=1) = 473/750 > 27/250 at BOTH the strict-OC and per-run-SSC states; EDT on the realized act refrains (−629666.7 vs −108000) under both senses; R1-state and R2-SIA smoke (−499000 vs −499500), R2-real undefined (no node-action-veridical node); with the draw coordinate md in the algebra, P_s(k|md) = 1/2 flat and V(md=1) = −499000 > −499500 = V(md=0): smoke"
    # ---- C1-15: CF observability sweep (extending CF-18).
    cf = {}
    for label, B, dn, les in [("E1-S3", E1_s3().B, "d", Eq("l", 1)), ("E1-tickle", E1_tickle().B, "d1", Eq("l", 1)), ("E2a", E2a_refclass().B, "d", Eq("l", 1)), ("E2c", E2c_tickle_population().B, "d", Eq("l", 1)),
                              ("E3-2pt", robots().B, "dS", Eq("t", "S")), ("E3-1pt", robots(two_points=False).B, "d", Eq("t", "S")), ("E8", fdt_sl().B, "dS", Eq("l", 1))]:
        Fm = dp.Fr(B); part = dp.S_partition(les)
        cf[label] = (dp.column_determined(Fm, dp.S_of(les)), dp.observable(Fm, part).observable, dp.observable(dp.Loc(B, dn), part).observable)
    assert all(v[0] for v in cf.values())
    assert cf["E1-S3"][1:] == (False, False) and cf["E1-tickle"][1:] == (True, True) and cf["E2a"][1:] == (False, False) and cf["E2c"][1:] == (False, False)
    assert cf["E3-2pt"][1:] == (True, True) and cf["E3-1pt"][1:] == (False, False) and cf["E8"][1:] == (True, True)
    out["C1-15"] = f"CF: lesion/type partition column-determined on every SL encoding; observable (Fr and Loc_d) exactly on the observation/two-point encodings: {cf}"
    # ---- Lemma 3′ sweep: on every roster row whose tree records at d for the row's C, the calibrated common-cause correlation is 0 or undefined.
    for r in roster():
        label, o, dn, C, les, act1, bad, mode = r
        if les is None: continue
        run = dp.Run(o.B, o.B.point(dn))if False else dp.Run(o.B, C)
        if dp.records(run, o.B.point(dn)).ok:
            for sense in ("strict", "per-run"):
                s, p = calibrated_point(o.B, C, dn, sense)
                if s is None: continue
                c1, c0 = state_cond(s, les, act1), state_cond(s, les, ~act1)
                assert c1 is None or c0 is None or dp.is_zero(c1 - c0), (label, sense, c1, c0)
    out["C1-4-sweep"] = "on every roster row recording at d, the κ-calibrated common-cause conditionals given the act are equal (or the act is null): Lemma 3′ holds on the recorded class"
    # ---- pooled-correlation identity (two-branch, two points; Lean candidate C1-pooled-correlation.lean)
    rho, g1, g0, q1, q0 = sp.symbols("rho g1 g0 q1 q0", positive=True)
    num1 = rho * q1; num0 = (1 - rho) * q0
    nu_m1 = num1 + num0; nu_m0 = rho * (1 - q1) + (1 - rho) * (1 - q0)
    corr = (rho * q1 * g1 + (1 - rho) * q0 * g0) / nu_m1 - (rho * (1 - q1) * g1 + (1 - rho) * (1 - q0) * g0) / nu_m0
    ident = (g1 - g0) * (q1 - q0) * rho * (1 - rho) / (nu_m1 * nu_m0)
    assert sp.simplify(corr - ident) == 0
    out["C1-pooled-identity"] = "two-branch tree with points d1 (q1), d0 (q0): ν(k|m=1) − ν(k|m=0) = (γ1−γ0)(q1−q0)ρ(1−ρ) / (ν(m=1)ν(m=0)) — sign = sign(q1−q0) when γ1 > γ0 [checked symbolically]"
    return out

# =============================================================================
# 5. main
# =============================================================================
def main():
    say("=== the C1 grid ===")
    rows = grid()
    say("\n=== targets ===")
    out = targets()
    for k, v in out.items():
        say(f"{k}: {v}")
    say("\nALL ASSERTIONS PASSED")
    return rows, out


# --- E13: the COMPULSION reading (Jiro's case 2: "it may not be possible for you to execute some strategies"):
#     one point d (O = ⊤) draws m_d; then the lesion overrides: realized m := 1 w.p. c_l, else m := m_d.
#     Worlds record (l, m, k) — the realized m only, unless record_draw=True adds the decision coordinate md.
def compulsion(rho=F(1,2), g0=F(1,100), g1=F(99,100), c1=F(9,10), c0=F(1,10), alpha=1000, beta=1000000, record_draw=False, state=None):
    m1, m0 = Eq("m", 1), Eq("m", 0)
    d = Point("d", state, TOP, [m1, m0])
    def r(w):
        return alpha * w["m"] - beta * w["k"]
    def leafk(l, m, md):
        g = g1 if l == 1 else g0
        def mk(k):
            w = W(l=l, m=m, k=k, md=md) if record_draw else W(l=l, m=m, k=k)
            return Leaf(w, r(w))
        return bern("k", g, mk(1), mk(0), coord="k")
    def after_draw(l, md):
        c = c1 if l == 1 else c0
        if md == 1:
            return leafk(l, 1, 1)
        return chance(("forced", c, leafk(l, 1, 0)), ("free", 1 - c, leafk(l, 0, 0)))
    def branch(l):
        return Decision(d, {m1: after_draw(l, 1), m0: after_draw(l, 0)})
    root = bern("l", rho, branch(1), branch(0), coord="l")
    return NS(B=dp.Problem(root, name="SL-compulsion" + ("+md" if record_draw else "")), d=d, m1=m1, m0=m0)

if __name__ == "__main__":
    main()
