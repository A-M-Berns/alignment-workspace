"""Adversary L1: two single-observation (O_d = T) instantiations of v2 (S1)+(S2)+(S3) in which the calibrated
state at the OC grades satisfies (S2).  Both fail Definition 7 recording — (A) by coverage (other agents' runs never
consult d: Yudkowsky-Soares's 'population of agents that use a different decision procedure'), (B) by two same-(O,A)
points differing only in cf (Remark 4.4).  Also (C) an independent recheck of L1-17's robot numbers."""
import sys
sys.path.insert(0, '[scrubbed]')
import dp
from dp import Eq, TOP, World as W, Dist, State, Point, Leaf, Decision, Problem, Procedure, chance
from fractions import Fraction as F
import sympy as sp
def hdr(s): print("\n" + "="*8, s)
K1 = Eq('k',1); M1, M0 = Eq('m',1), Eq('m',0)

# ---------------- A. the third population: Eve (procedure) w.p. pi, lesion-following automaton w.p. 1-pi
g1, g0, alpha, beta = F(99,100), F(1,100), 1000, 10**6
rho, pi = F(1,2), F(1,2)
def r(w): return alpha*w['m'] - beta*w['k']
def cancer(tau, l, m):
    gam = g1 if l == 1 else g0
    mk = lambda k: Leaf(W(tau=tau, l=l, m=m, k=k), r(W(tau=tau, l=l, m=m, k=k)))
    return chance(('1', gam, mk(1)), ('0', 1-gam, mk(0)), events={'1': Eq('k',1), '0': Eq('k',0)})
def lesion_then_cancer(tau, m_of_l):
    return chance(('1', rho, cancer(tau, 1, m_of_l(1))), ('0', 1-rho, cancer(tau, 0, m_of_l(0))), events={'1': Eq('l',1), '0': Eq('l',0)})
d = Point('d', None, TOP, [M1, M0])
eve = Decision(d, {M1: lesion_then_cancer('E', lambda l: 1), M0: lesion_then_cancer('E', lambda l: 0)})   # query BEFORE the lesion draw: one d-node
auto = lesion_then_cancer('A', lambda l: l)                                                                 # automaton smokes iff lesioned
B = Problem(chance(('E', pi, eve), ('A', 1-pi, auto), events={'E': Eq('tau','E'), 'A': Eq('tau','A')}), name='SL-third-population')
print("validate:", B.validate(), "| d-nodes:", len(B.fibers()['d']), "| strongly fair:", dp.is_strongly_fair(B), "| almost fair:", dp.is_almost_fair(B))
q = dp.sym('q', 0, 1)
procs = {'refrain': Procedure({d: 'm=0'}), 'smoke': Procedure({d: 'm=1'}), 'mixed q': Procedure({d: {'m=1': q, 'm=0': 1-q}})}
for name, C in procs.items():
    hdr(f"A. third population, C = {name}")
    run = dp.Run(B, C)
    rec = dp.records(run, d)
    print("  covers d:", dp.covers(run, d), "| records at d:", rec.ok, "" if rec.ok else f"({len(rec.violations)} violations; e.g. {rec.violations[:1]})")
    print("  every d-node subtree-veridical:", all(dp.subtree_veridical(B, qn) for qn in B.fibers()['d']))
    gap = sp.simplify(run.nu_cond(K1, M1) - run.nu_cond(K1, M0))
    print("  population nu(k|m=1) - nu(k|m=0) =", gap)
    s = dp.calibrated_state(B, C, d, 'strict')
    Bc = dp.with_states(B, {d: s})
    print("  strict state: P(k|m=1)-P(k|m=0) =", sp.simplify(s.P_of(K1 & M1)/s.P_of(M1) - s.P_of(K1 & M0)/s.P_of(M0)), "| P_s(m=1) =", sp.simplify(s.P_of(M1)), "| P_s(tau=E) =", s.P_of(Eq('tau','E')))
    print("  (S2) holds at the strictly calibrated state:", not dp.is_zero(sp.simplify(s.P_of(K1 & M1)/s.P_of(M1) - s.P_of(K1 & M0)/s.P_of(M0))))
    print("  strict:", dp.strict_oc(Bc, C).points['d'].status, "| masked:", dp.masked_oc(Bc, C, d).status, "| limit:", dp.limit_oc(Bc, C).points['d'].status)
    for sense in ('per-run', 'per-occurrence'):
        s2 = dp.calibrated_state(B, C, d, sense)
        try:
            g2 = sp.simplify(s2.P_of(K1 & M1)/s2.P_of(M1) - s2.P_of(K1 & M0)/s2.P_of(M0))
        except ZeroDivisionError:
            g2 = 'undefined (a conditional on a null action)'
        print(f"  {sense} SSC state at d: P(k|m=1)-P(k|m=0) = {g2} ; status of the strict state under {sense}: {dp.ssc(Bc, C, sense=sense).points['d'].status}")
    pt = Point('d', s, TOP, [M1, M0])
    ev = dp.edt_values(pt)
    print("  evidential act values at the strict state:", {k: sp.simplify(v) for k, v in ev.items()}, "->", dp.EDT(pt), "| T_EDT(C) at this state:", dp.T_EDT(C, Bc).ok)
    t1 = dp.theorem1_condition(B, C, d); t2 = dp.theorem2_evaluator(B, C, d)
    print("  Thm-1 forcing sums:", {k: sp.simplify(v) for k, v in t1['weighted'].items()}, "| Thm-2 deviation V_B(C[d->a]):", {k: sp.simplify(v) for k, v in t2['deviation'].items()})
    # classical CDT: hold P_s(l,k) fixed, force m
    def cf_state(a):   # classical CDT: hold P_s(tau, l, k) fixed, force m = a on every atom (worlds outside the tree's support allowed)
        Ps = {}
        for tau in ('E','A'):
            for l in (0,1):
                for k in (0,1):
                    pr = s.P_of(Eq('tau', tau) & Eq('l', l) & Eq('k', k))
                    if not dp.is_zero(pr): Ps[W(tau=tau, l=l, m=a, k=k)] = pr
        return State(Dist(Ps), r, name=f"cf[m={a}]")
    dc = Point('d', State(s.P, r, cf={'m=1': cf_state(1), 'm=0': cf_state(0)}), TOP, [M1, M0]); dc.check_cf_success()
    cv = dp.cdt_values(dc); print("  classical-CDT act values:", {k: sp.simplify(v) for k, v in cv.items()}, "->", dp.CDT(dc))
    print("  V_B =", sp.simplify(dp.value(B, C)))
print("\n  optimum V_B:", dp.optimal_value(B), " (smoke, by alpha*pi)")

# ---------------- B. two same-(O,A) points differing only in cf (Remark 4.4), numeric instance
hdr("B. cf-distinguished points at O = T: rho=1/2, gamma=(4/5,1/5), alpha=1, beta=5")
g1, g0, alpha, beta, rho = F(4,5), F(1,5), 1, 5, F(1,2)
def r2(w): return alpha*w['m'] - beta*w['k']
def canc(l, m):
    gam = g1 if l == 1 else g0
    mk = lambda k: Leaf(W(l=l, m=m, k=k), r2(W(l=l, m=m, k=k)))
    return chance(('1', gam, mk(1)), ('0', 1-gam, mk(0)), events={'1': Eq('k',1), '0': Eq('k',0)})
q1, q0 = sp.symbols('q1 q0')
# plain sympy for the population law (points differ only in cf; both strict states equal nu(.|T) = nu)
P_m1 = rho*q1 + (1-rho)*q0
P_k_m1 = rho*q1*g1 + (1-rho)*q0*g0
P_m0 = rho*(1-q1) + (1-rho)*(1-q0)
P_k_m0 = rho*(1-q1)*g1 + (1-rho)*(1-q0)*g0
gap = sp.simplify(P_k_m1/P_m1 - P_k_m0/P_m0)
tie = sp.solve(sp.Eq(alpha - beta*gap, 0), q1)
print("  strict state at either point = nu; (S2) gap(q1,q0) =", sp.factor(gap))
print("  T_EDT tie (V(m=1)=V(m=0)) solved for q1:", tie)
for q0v in (F(1,10), F(1,4), F(1,2)):
    q1v = [sp.nsimplify(t.subs(q0, q0v)) for t in tie if 0 <= t.subs(q0, q0v) <= 1]
    print(f"    q0={q0v}: q1 on the tie = {q1v}; gap = {[sp.nsimplify(gap.subs({q0:q0v, q1:v})) for v in q1v]} (= alpha/beta = 1/5)")
# toolkit check: build the two points with distinct cf objects, strict and per-run states
q0v, q1v = F(1,3), F(2,3)   # rational point on the tie: with s = q0+q1 = 1, q1-q0 = s(2-s)/3 = 1/3
print("  rational tie point (q1,q0) = (2/3,1/3): gap =", sp.nsimplify(gap.subs({q0: q0v, q1: q1v})), "(= 1/5)")
def cfs(tag):
    return {'m=1': State(Dist({W(l=0,m=1,k=0): 1}), r2, name=f'cf1-{tag}'), 'm=0': State(Dist({W(l=0,m=0,k=0): 1}), r2, name=f'cf0-{tag}')}
d1 = Point('d1', State(Dist({W(l=0,m=0,k=0): 1}), r2, cf=cfs('a')), TOP, [M1, M0])   # placeholder P,V; replaced by calibrated states below
d0 = Point('d0', State(Dist({W(l=0,m=0,k=0): 1}), r2, cf=cfs('b')), TOP, [M1, M0])
B2 = Problem(chance(('1', rho, Decision(d1, {M1: canc(1,1), M0: canc(1,0)})), ('0', 1-rho, Decision(d0, {M1: canc(0,1), M0: canc(0,0)})), events={'1': Eq('l',1), '0': Eq('l',0)}), name='SL-cf-two-points')
print("  validate:", B2.validate())
C2 = Procedure({d1: {'m=1': q1v, 'm=0': 1-q1v}, d0: {'m=1': q0v, 'm=0': 1-q0v}})
run2 = dp.Run(B2, C2)
for n, pt in (('d1', d1), ('d0', d0)):
    print(f"  covers {n}:", dp.covers(run2, pt), "| records:", dp.records(run2, pt).ok)
    ss = dp.calibrated_state(B2, C2, pt, 'strict'); sr = dp.calibrated_state(B2, C2, pt, 'per-run')
    gs = ss.P_of(K1 & M1)/ss.P_of(M1) - ss.P_of(K1 & M0)/ss.P_of(M0); gr = sr.P_of(K1 & M1)/sr.P_of(M1) - sr.P_of(K1 & M0)/sr.P_of(M0)
    print(f"    strict-OC state: P(l=1)={ss.P_of(Eq('l',1))}, (S2) gap={sp.nsimplify(gs)} ; per-run-SSC state: P(l=1)={sr.P_of(Eq('l',1))}, (S2) gap={sp.nsimplify(gr)}")
Bc2 = dp.with_states(B2, {d1: dp.calibrated_state(B2, C2, d1, 'strict'), d0: dp.calibrated_state(B2, C2, d0, 'strict')})
print("  at the strict states: strict_oc ok:", dp.strict_oc(Bc2, C2).ok, "| T_EDT(C2):", dp.T_EDT(C2, Bc2).ok, "| per-run SSC ok:", dp.ssc(Bc2, C2, sense='per-run').ok)
print("  V_B(C2) =", dp.value(B2, C2), "| Thm-2 deviation at d1:", {k: sp.nsimplify(v) for k, v in dp.theorem2_evaluator(B2, C2, d1)['deviation'].items()})

# ---------------- C. robots recheck (independent of L1's script)
hdr("C. P01 robots: independent recheck of p*(eps), V_B values, and the per-type-payoff alternative")
p, e = sp.symbols('p eps', positive=True)
VS = (-90*p + 10*e)/(p + e); VR = -100*(1-p)/((1-p) + (1-e))
sol = [s for s in sp.solve(sp.Eq(VS, VR), p)]
print("  equilibrium p(eps):", [sp.simplify(s) for s in sol])
ps = [s for s in sol if s.subs(e, F(1,100)) > 0][0]
print("  at eps=1/100: p* =", sp.N(ps.subs(e, F(1,100)), 8), "| V_B(EDT-eps) =", sp.N((-50 + 5*ps - e/2).subs(e, F(1,100)), 6), "| V_B(CDT robots) = -45 | merged V_B(q) = -50 + 4.5 q")
print("  NSL smoke prob eps (not eps/2) is what k=1.5 needs: first order 8p - 12 eps = 0 -> p = 1.5 eps")

# ---------------- A'. Lewis's partly-rational agent: others observe their lesion-dependent love of smoking (tickle points p1, p0,
# payoff alpha_l m - beta k with alpha_1 = 1000 > 0 > alpha_0 = -1, run by calibrated EDT), I share the payoff law but observe nothing (O_d = T)
hdr("A'. calibrated reference class (C1's E2c shape): my point d at O=T, others at tickle points; TB numbers, rho = pi = 1/2")
g1, g0, beta = F(99,100), F(1,100), 10**6
al = {1: 1000, 0: -1}
def rl(w): return al[w['l']]*w['m'] - beta*w['k']
def canc2(who, l, m):
    gam = g1 if l == 1 else g0
    mk = lambda k: Leaf(W(who=who, l=l, m=m, k=k), rl(W(who=who, l=l, m=m, k=k)))
    return chance(('1', gam, mk(1)), ('0', 1-gam, mk(0)), events={'1': Eq('k',1), '0': Eq('k',0)})
dme = Point('d', None, TOP, [M1, M0])
p1, p0 = Point('p1', None, Eq('l',1), [M1, M0]), Point('p0', None, Eq('l',0), [M1, M0])
me = Decision(dme, {M1: chance(('1', F(1,2), canc2('me',1,1)), ('0', F(1,2), canc2('me',0,1)), events={'1': Eq('l',1), '0': Eq('l',0)}),
                    M0: chance(('1', F(1,2), canc2('me',1,0)), ('0', F(1,2), canc2('me',0,0)), events={'1': Eq('l',1), '0': Eq('l',0)})})
other = chance(('1', F(1,2), Decision(p1, {M1: canc2('o',1,1), M0: canc2('o',1,0)})), ('0', F(1,2), Decision(p0, {M1: canc2('o',0,1), M0: canc2('o',0,0)})), events={'1': Eq('l',1), '0': Eq('l',0)})
BL = Problem(chance(('me', F(1,2), me), ('o', F(1,2), other), events={'me': Eq('who','me'), 'o': Eq('who','o')}), name='SL-Lewis-refclass')
print("  validate:", BL.validate(), "| d-nodes:", len(BL.fibers()['d']))
for mine in ('m=0', 'm=1'):
    CL = Procedure({dme: mine, p1: 'm=1', p0: 'm=0'})
    runL = dp.Run(BL, CL)
    sts = {pt: dp.calibrated_state(BL, CL, pt, 'strict') for pt in (dme, p1, p0)}
    BLc = dp.with_states(BL, sts)
    sd = sts[dme]
    gapd = sp.simplify(sd.P_of(K1 & M1)/sd.P_of(M1) - sd.P_of(K1 & M0)/sd.P_of(M0))
    ev = dp.edt_values(Point('d', sd, TOP, [M1, M0]))
    print(f"  C(d)={mine}: covers d {dp.covers(runL, dme)} | records d {dp.records(runL, dme).ok} | strict_oc all points ok {dp.strict_oc(BLc, CL).ok} | limit ok {dp.limit_oc(BLc, CL).ok} | (S2) gap at d {gapd} | EDT values at d {dict((k, sp.simplify(v)) for k, v in ev.items())} | T_EDT(C) {dp.T_EDT(CL, BLc).ok} | per-run SSC status at d {dp.ssc(BLc, CL, sense='per-run').points['d'].status} | V_B {dp.value(BL, CL)}")
    srun = dp.calibrated_state(BL, CL, dme, 'per-run')
    try: gpr = sp.simplify(srun.P_of(K1 & M1)/srun.P_of(M1) - srun.P_of(K1 & M0)/srun.P_of(M0))
    except ZeroDivisionError: gpr = 'undefined (null act)'
    print(f"     per-run SSC state at d: P(who=me) = {srun.P_of(Eq('who','me'))}, (S2) gap = {gpr}")
t2 = dp.theorem2_evaluator(BL, Procedure({dme: 'm=0', p1: 'm=1', p0: 'm=0'}), dme)
print("  Thm-2 deviation at d:", {k: sp.simplify(v) for k, v in t2['deviation'].items()}, "| optimum:", dp.optimal_value(BL))

# ---------------- D. P01 robots: two same-(O,A) points distinguished only by cf, pooled calibrated states, the T_EDT tie
hdr("D. robots, two O=T points differing only in cf, pooled strict states: the calibrated-and-approved evidential tie vs the causal referents")
qS, qN = sp.symbols('qS qN')
# pooled law: SL w.p. 1/2 smokes qS (killed), NSL w.p. 1/2 smokes qN (alive); payoffs P01
P_sm = (qS + qN)/2; V_sm = ((qS*(-90)) + (qN*(-1)))/2 / P_sm
P_rf = ((1-qS) + (1-qN))/2; V_rf = (((1-qS)*(-100)) + ((1-qN)*0))/2 / P_rf
tie = sp.solve(sp.Eq(sp.simplify(V_sm - V_rf), 0), qS)
print("  pooled V(smoke) =", sp.simplify(V_sm), "| pooled V(refrain) =", sp.simplify(V_rf))
print("  tie qS(qN):", [sp.simplify(t) for t in tie])
for qNv in (F(1,100), F(1,10)):
    qSv = [sp.nsimplify(t.subs(qN, qNv)) for t in tie if 0 <= t.subs(qN, qNv) <= 1]
    print(f"    qN={qNv}: qS on the tie = {qSv} ({[sp.N(v,5) for v in qSv]}); V_B = {[sp.nsimplify(-50 + 5*v - qNv/2) for v in qSv]} vs CDT robots -45; deviation at dSL: smoke -90 > refrain -100")
print("ALL OK")
