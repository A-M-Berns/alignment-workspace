"""Repair L1: three checks behind the dispositions.
(1) Tremble-(ii) (realized act as the action; L1-20): does SSC screen the correlation?  Per-run and per-occurrence SSC states at d,
    their (S2) gap, and the status of the strict state under both SSC senses.  Compare with the reference-class tree (adversary §A),
    where SSC does screen.  Decides whether the reviewer's closing compression ("uncovered or overwritten ... screened at SSC") is right.
(2) WAR difference V_B(C[d->smoke]) - V_B(C[d->refrain]) on the enumerated S3 tree, the reference-class tree and the tremble tree:
    the WOUNDED form of L1-10/L1-29 (= alpha on recording trees, = alpha * pi and = alpha*(1-E[t_l]) otherwise; sign positive).
(3) Reference-class tree at the masked grade for deterministic C via an interior self-model (the L1-12(i) rider applied)."""
import sys
sys.path.insert(0, '[scrubbed]')
import dp
from dp import Eq, TOP, World as W, Dist, State, Point, Leaf, Decision, Problem, Procedure, chance
from fractions import Fraction as F
import sympy as sp
def hdr(s): print("\n" + "="*8, s)
K1 = Eq('k',1)

# ---------- (1) tremble-(ii), L1's numbers: rho=1/2, gamma=(4/5,1/5), alpha=1, beta=5, t1=3/5, t0=1/10
rho, g1, g0, alpha, beta, t1, t0 = F(1,2), F(4,5), F(1,5), 1, 5, F(3,5), F(1,10)
def r_tr(w): return alpha*w['mp'] - beta*w['k']
def cancer(l, m, mp):
    gam = g1 if l == 1 else g0
    return chance(('1', gam, Leaf(W(l=l,m=m,mp=mp,k=1), r_tr(W(l=l,m=m,mp=mp,k=1)))), ('0', 1-gam, Leaf(W(l=l,m=m,mp=mp,k=0), r_tr(W(l=l,m=m,mp=mp,k=0)))), events={'1': Eq('k',1), '0': Eq('k',0)})
def after_draw(l, m):
    if m == 1: return cancer(l, 1, 1)
    tl = t1 if l == 1 else t0
    return chance(('flip', tl, cancer(l, 0, 1)), ('stay', 1-tl, cancer(l, 0, 0)), events={'flip': Eq('mp',1), 'stay': Eq('mp',0)})
A1, A0 = Eq('mp',1), Eq('mp',0)
d = Point('d', None, TOP, [A1, A0])
Btr = Problem(chance(('1', rho, Decision(d, {A1: after_draw(1,1), A0: after_draw(1,0)})), ('0', 1-rho, Decision(d, {A1: after_draw(0,1), A0: after_draw(0,0)})), events={'1': Eq('l',1), '0': Eq('l',0)}), name='SL-tremble-ii')
q = dp.sym('q', 0, 1)
hdr("(1) tremble-(ii): SSC grades")
for name, C in (('mixed q', Procedure({d: {'mp=1': q, 'mp=0': 1-q}})), ('refrain', Procedure({d: 'mp=0'})), ('smoke', Procedure({d: 'mp=1'}))):
    run = dp.Run(Btr, C)
    print(f"  C = {name}: covers d {dp.covers(run, d)} | records {dp.records(run, d).ok} | mu(occ(d)) = {sp.simplify(run.mu_occ(d)) if hasattr(run,'mu_occ') else 'n/a'}")
    s_strict = dp.calibrated_state(Btr, C, d, 'strict')
    Bc = dp.with_states(Btr, {d: s_strict})
    for sense in ('per-run', 'per-occurrence'):
        s2 = dp.calibrated_state(Btr, C, d, sense)
        try:
            gap = sp.simplify(s2.P_of(K1 & A1)/s2.P_of(A1) - s2.P_of(K1 & A0)/s2.P_of(A0))
        except ZeroDivisionError:
            gap = 'undefined (null action)'
        same = all(dp.is_zero(sp.simplify(s2.P_of(X) - s_strict.P_of(X))) for X in (A1, K1, K1 & A1, Eq('l',1)))
        print(f"     {sense:15s}: (S2) gap at the SSC state = {gap} | SSC state == strict state on (mp,k,l): {same} | strict state's status under {sense}: {dp.ssc(Bc, C, sense=sense).points['d'].status}")
    if name == 'mixed q':
        ev = dp.edt_values(Point('d', s_strict, TOP, [A1, A0]))
        print("     evidential difference at the (common) calibrated state:", sp.simplify(ev['mp=1'] - ev['mp=0']), "| masked status:", dp.masked_oc(Bc, C, d).status)

# ---------- reference-class tree (adversary §A) for comparison, per-occurrence included
hdr("(1b) reference-class tree (adversary §A): SSC grades, both senses")
g1, g0, alpha, beta = F(99,100), F(1,100), 1000, 10**6
rho, pi = F(1,2), F(1,2)
M1, M0 = Eq('m',1), Eq('m',0)
def r(w): return alpha*w['m'] - beta*w['k']
def canc(tau, l, m):
    gam = g1 if l == 1 else g0
    mk = lambda k: Leaf(W(tau=tau, l=l, m=m, k=k), r(W(tau=tau, l=l, m=m, k=k)))
    return chance(('1', gam, mk(1)), ('0', 1-gam, mk(0)), events={'1': Eq('k',1), '0': Eq('k',0)})
def ltc(tau, m_of_l):
    return chance(('1', rho, canc(tau, 1, m_of_l(1))), ('0', 1-rho, canc(tau, 0, m_of_l(0))), events={'1': Eq('l',1), '0': Eq('l',0)})
dA = Point('d', None, TOP, [M1, M0])
eve = Decision(dA, {M1: ltc('E', lambda l: 1), M0: ltc('E', lambda l: 0)})
BA = Problem(chance(('E', pi, eve), ('A', 1-pi, ltc('A', lambda l: l)), events={'E': Eq('tau','E'), 'A': Eq('tau','A')}), name='SL-refclass')
for name, C in (('mixed q', Procedure({dA: {'m=1': q, 'm=0': 1-q}})), ('refrain', Procedure({dA: 'm=0'}))):
    s_strict = dp.calibrated_state(BA, C, dA, 'strict'); Bc = dp.with_states(BA, {dA: s_strict})
    for sense in ('per-run', 'per-occurrence'):
        s2 = dp.calibrated_state(BA, C, dA, sense)
        try: gap = sp.simplify(s2.P_of(K1 & M1)/s2.P_of(M1) - s2.P_of(K1 & M0)/s2.P_of(M0))
        except ZeroDivisionError: gap = 'undefined (null action)'
        print(f"  C = {name:8s} {sense:15s}: (S2) gap at SSC state = {gap} | P_SSC(tau=E) = {s2.P_of(Eq('tau','E'))} | strict state's status: {dp.ssc(Bc, C, sense=sense).points['d'].status}")

# ---------- (3) reference-class tree, deterministic C at the masked grade via an interior self-model
hdr("(3) reference-class tree, C = refrain, masked grade: state nu_{C[d->m]}(.|T) at interior self-model m(smoke)=1/10")
Cref = Procedure({dA: 'm=0'})
m_int = F(1,10)
Cm = Procedure({dA: {'m=1': m_int, 'm=0': 1-m_int}})
s_m = dp.calibrated_state(BA, Cm, dA, 'strict')          # = nu_{B, C[d->m]}(. | T): the masked candidate state
Bm = dp.with_states(BA, {dA: s_m})
gapm = sp.simplify(s_m.P_of(K1 & M1)/s_m.P_of(M1) - s_m.P_of(K1 & M0)/s_m.P_of(M0))
print("  masked_oc status of that state for C = refrain:", dp.masked_oc(Bm, Cref, dA).status, "| (S2) gap there:", gapm, "| P_s(m=1) =", s_m.P_of(M1))
ev = dp.edt_values(Point('d', s_m, TOP, [M1, M0])); print("  evidential values at that state:", {k: sp.nsimplify(v) for k, v in ev.items()}, "->", dp.EDT(Point('d', s_m, TOP, [M1, M0])))

# ---------- (2) WAR difference in general form
hdr("(2) V_B(C[d->smoke]) - V_B(C[d->refrain]) on three trees")
# enumerated S3 (records): use examples.smoking_lesion_S3 if available, else build
try:
    import examples
    BS3, dS3 = examples.smoking_lesion_S3(rho=F(1,2), g1=F(99,100), g0=F(1,100), alpha=1000, beta=10**6)[:2]
except Exception as e:
    BS3 = None; print("  (examples.smoking_lesion_S3 not used:", repr(e)[:80], ")")
if BS3 is None:
    dS = Point('d', None, TOP, [M1, M0])
    def canc3(l, m):
        gam = g1 if l == 1 else g0
        mk = lambda k: Leaf(W(l=l, m=m, k=k), r(W(l=l, m=m, k=k)))
        return chance(('1', gam, mk(1)), ('0', 1-gam, mk(0)), events={'1': Eq('k',1), '0': Eq('k',0)})
    BS3 = Problem(chance(('1', rho, Decision(dS, {M1: canc3(1,1), M0: canc3(1,0)})), ('0', 1-rho, Decision(dS, {M1: canc3(0,1), M0: canc3(0,0)})), events={'1': Eq('l',1), '0': Eq('l',0)}), name='S3')
    dS3 = dS
for label, B_, d_, a1, a0 in (('enumerated S3 (records)', BS3, dS3, 'm=1', 'm=0'), ('reference class (coverage fails)', BA, dA, 'm=1', 'm=0'), ('tremble-(ii) (action-veridicality fails)', Btr, d, 'mp=1', 'mp=0')):
    diff = sp.simplify(dp.value(B_, Procedure({d_: a1})) - dp.value(B_, Procedure({d_: a0})))
    print(f"  {label:42s}: {diff}")
print("  expected: alpha = 1000 ; alpha*pi = 500 ; alpha*(1 - E[t_l]) = 1*(1 - (3/5+1/10)/2) = 13/20")
print("ALL OK")
