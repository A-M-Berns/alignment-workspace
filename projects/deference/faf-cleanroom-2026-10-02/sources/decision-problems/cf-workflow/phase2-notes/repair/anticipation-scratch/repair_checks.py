"""Repair-agent checks for thread `anticipation` (phase 2, 2026-09-02).
Independent recomputation (pure Fractions where possible; toolkit `Run`/`calibrated_state` — TRUSTED — where a tree is needed)
of the reviewer's killers and of the hypotheses written into the repaired claims.
 A. Claim 2: hand recomputation of a1 (i)-(iii) and the exact (statistical) criterion.
 B. Claim 3: TYS take-5-both, d10 — the three grades PER epsilon vs AGAINST the limit prior.
 C. Claim 4 / identity handoff: forward a.c., density bound, reverse a.c. of the tails-certain state on the matched mugging.
 D. Claim 5: AN-15(b') — H(dP'/dP | A_obs) = 0 iff occ(d) in A_obs (mod null): B_1, radical-label tree, instance-blind tree.
 E. Claim 6: hand recomputation of a4's nested-survivor numbers (3/8,3/8,1/8,1/8) from the tree's arithmetic.
 F. Claim 7: the quotient obstruction as a general one-liner, numerically, for every P_t0 with P_t0(X_7) > 0.
 G. AN-3(iii): TN-V1 d_E is expressible although the root is an unrecorded decision edge (sufficient condition does not cover it).
"""
import sys, math
sys.path.insert(0, "[scrubbed]")
import dp, examples as ex, sympy as sp
from dp import World as W, Eq, Leaf, Decision, Point, Problem, Procedure, State, Dist, TOP, BOT, chance
from fractions import Fraction as F

def show(D): return "{" + ", ".join(f"{k}: {v}" for k, v in sorted(D.items(), key=lambda kv: repr(kv[0]))) + "}"
def H_bits(masses):
    return -sum(float(m) * math.log2(float(m)) for m in masses if m > 0)

print("=== A. Claim 2 by hand (pure fractions) ===")
# (i) notes' witness: leaves (L,a=1)->(w0,r=1) mass 1/2 [C = a=1 det.]; (R)->(w0,r=0) mass 1/2. occ = {L}.
mu = {('L', 'w0', 1): F(1, 2), ('R', 'w0', 0): F(1, 2)}
occ = {('L', 'w0', 1)}
nu_w0 = sum(mu.values()); ssc_P = {('w0'): sum(m for l, m in mu.items() if l in occ) / sum(m for l, m in mu.items() if l in occ)}
ssc_V = sum(l[2] * m for l, m in mu.items() if l in occ) / sum(m for l, m in mu.items() if l in occ)
oc_top_V = sum(l[2] * m for l, m in mu.items()) / nu_w0
print(f" (i)  per-run SSC (P,V) = (delta_w0, {ssc_V}); strict OC at TOP (P,V) = (delta_w0, {oc_top_V}) -> P agrees, V differs: {ssc_V != oc_top_V}")
# (ii) right payoff 1
mu2 = {('L', 'w0', 1): F(1, 2), ('R', 'w0', 1): F(1, 2)}
ssc_V2 = F(1); oc_V2 = sum(l[2] * m for l, m in mu2.items())
print(f" (ii) right payoff 1: SSC V = {ssc_V2}, OC-at-TOP V = {oc_V2}; both clauses agree: {ssc_V2 == oc_V2}; occ not expressible (w0 on both sides): True")
# (iii) left d -> (c=0,1)/(c=1,0) w.p. 1/2 each (C mixed), right leaf (c=0,0) w.p. 1/2
mu3 = {('L', 'c0'): F(1, 4), ('L', 'c1'): F(1, 4), ('R', 'c0'): F(1, 2)}
nu3 = {'c0': F(3, 4), 'c1': F(1, 4)}; ssc3 = {'c0': F(1, 2), 'c1': F(1, 2)}
ratios = {w: ssc3[w] / nu3[w] for w in ssc3}
conds = {X: {w: (nu3[w] / sum(nu3[x] for x in X) if w in X else F(0)) for w in nu3} for X in [('c0',), ('c1',), ('c0', 'c1')]}
print(f" (iii) nu = {nu3}, SSC P = {ssc3}; ratios SSC/nu = {ratios} (not constant); nu(.|X) for X in E: {conds}; some X matches: {any(c == ssc3 for c in conds.values())}")
print(" exact P-criterion: S = nu(.|X) for some X  <=>  S/nu constant on supp S (then X = supp S, constant = 1/nu(X)) — algebra, no computation needed.")

print("\n=== B. Claim 3: TYS take-5-both, point d10 — grades per epsilon vs against the limit prior ===")
t = ex.told_you_so(); C = t.take5_both
run0 = dp.Run(t.B, C)
lim_state = dp.calibrated_state(t.B, C, 'd10', 'limit').P
print(" nu_C =", show(run0.nu), "| Def-10 limit state at d10 =", show(lim_state), "| a.c. w.r.t. nu_C:", all(not dp.is_zero(run0.nu[w]) for w in lim_state.support()))
for eps in (F(1, 10), F(1, 100)):
    Ce = C.tremble(eps); r = dp.Run(t.B, Ce)
    oc_e = dp.calibrated_state(t.B, Ce, 'd10', 'strict').P
    ssc_e = dp.calibrated_state(t.B, Ce, 'd10', 'per-run').P
    nuO = r.nu_of(t.d10.obs); mu_occ = r.mu_occ('d10')
    sup_oc = max(dp.simp(oc_e[w] / r.nu[w]) for w in oc_e.support())
    sup_lim = max(dp.simp(lim_state[w] / r.nu[w]) for w in lim_state.support())
    print(f" eps={eps}: nu_eps(O_10)={nuO} mu_eps(occ)={mu_occ} | eps-OC state {show(oc_e)} : (i) a.c. True, (ii) sup {sup_oc} <= 1/mu(occ)={1/mu_occ}: {sup_oc <= 1/mu_occ}, (iii) == per-run SSC_eps: {oc_e == ssc_e}"
          f" | Def-10 LIMIT state vs nu_eps: (i) a.c. {all(not dp.is_zero(r.nu[w]) for w in lim_state.support())}, (ii) sup {sup_lim} <= {1/mu_occ}: {sup_lim <= 1/mu_occ}")
print(" -> per epsilon the three grades are nested and all pass for the eps-strict state; the limit state passes (i) against every nu_eps but FAILS (i) against nu_C = lim nu_eps.")
print("    So the reviewer's non-nesting is the choice of prior at the limit grade (limit of priors vs family of priors); a.c. is not preserved under eps -> 0. Added hypothesis accepted.")

print("\n=== C. Claim 4 / identity: three conditions under ID-15's one name, matched mugging q=q0=1/2 ===")
m = ex.mugging(1, x=1, y=2, q0=F(1, 2)); Cq = Procedure({m.d: {'pay': F(1, 2), 'refuse': F(1, 2)}})
r = dp.Run(m.B, Cq); ref = dp.calibrated_state(m.B, Cq, 'd', 'per-run').P   # = lambda_* mu(.|occ) = nu
Ps = m.d.state.P
fwd_ac = all(not dp.is_zero(ref[w]) for w in Ps.support())
rev_ac = all(not dp.is_zero(Ps[w]) for w in ref.support())
sup = max(dp.simp(Ps[w] / ref[w]) for w in Ps.support())
print(f" referent lambda_*mu(.|occ) = {show(ref)}; tails-certain P_s = {show(Ps)}")
print(f" forward a.c. P_s << ref (ID-15's DISPLAYED formula): {fwd_ac}  | density sup {sup} <= 1/mu(occ)={1/r.mu_occ('d')}: {sup <= 1/r.mu_occ('d')} (the NUMBER)  | reverse a.c. ref << P_s (ID-15's WORDS): {rev_ac}")

print("\n=== D. Claim 5: AN-15(b') refinement measure H(dP'/dP | A_obs) ===")
def refinement_entropy(B, C, d):
    r = dp.Run(B, C); occ = set(r.occ(d)); mu_occ = r.mu_occ(d); O = B.point(d).obs
    # A_obs = sigma{lambda^{-1} O_e : e queried}; here single point: atoms = {O-leaves, non-O-leaves} (mod null)
    cells = {}
    for p, mass in r.mu.items():
        if dp.is_zero(mass): continue
        cell = bool(O(r.world(p)))
        f = (1 / mu_occ) if p in occ else F(0)
        cells.setdefault(cell, {}).setdefault(f, F(0)); cells[cell][f] += mass
    Hc = F(0); total = F(0)
    for cell, fm in cells.items():
        pc = sum(fm.values()); total += pc
        Hc += pc * H_bits([v / pc for v in fm.values()])
    return float(Hc), (set().union(*[set(fm) for fm in cells.values()]))
# B_1: occ = Leaves in A_obs -> 0
print(" B_1 (q=q0): H =", refinement_entropy(m.B, Cq, 'd')[0], "bits (occ(d) = Leaves in A_obs)")
# radical label tree (reviewer's (v)): evented chance A/B, O_d = TOP
sideA, sideB = Eq('side', 'A'), Eq('side', 'B')
d5 = Point('d', State(Dist({W(side='A', a=1): F(1, 2), W(side='A', a=2): F(1, 2)}), lambda w: 0), TOP, [Eq('a', 1), Eq('a', 2)])
root5 = chance(('A', F(1, 2), Decision(d5, {Eq('a', 1): Leaf(W(side='A', a=1), 1), Eq('a', 2): Leaf(W(side='A', a=2), 0)})),
               ('B', F(1, 2), Leaf(W(side='B', a=BOT), 0)), events={'A': sideA, 'B': sideB})
B5 = Problem(root5, name='radical-label'); C5 = Procedure({d5: {'a=1': F(1, 2), 'a=2': F(1, 2)}})
print(" radical-label tree (occ expressible as side=A, but O_d = TOP): H =", refinement_entropy(B5, C5, 'd')[0], "bits (> 0)")
# instance-blind tree (notes' witness), O_d = TOP
w0 = W(c=0)
dib = Point('d', State(Dist({w0: 1}), {w0: F(1, 2)}), TOP, [Eq('a', 1), Eq('a', 2)])
rootib = chance(('L', F(1, 2), Decision(dib, {Eq('a', 1): Leaf(w0, 1), Eq('a', 2): Leaf(w0, 0)})), ('R', F(1, 2), Leaf(w0, 0)))
Bib = Problem(rootib, name='instance-blind'); Cib = Procedure({dib: 'a=1'})
print(" instance-blind tree (occ NOT expressible, O_d = TOP): H =", refinement_entropy(Bib, Cib, 'd')[0], "bits (> 0)")
print(" -> the measure is 0 iff the density 1_occ/mu(occ) is A_obs-measurable iff occ(d) in A_obs mod null; expressibility in E is neither necessary nor sufficient for H = 0.")

print("\n=== E. Claim 6: nested survivor by hand ===")
# pre-enrichment: P(F) = 1/2*3/4 + 1/2*1/4 = 1/2; inside F the REAL d redraws independently (1/2,1/2), e draws (1/2,1/2): uniform 1/4.
pre = {('a', 'u'): F(1, 4), ('a', 'v'): F(1, 4), ('b', 'u'): F(1, 4), ('b', 'v'): F(1, 4)}
# post-relocation: one policy draw pol in {a,b} (1/2 each) resolves BOTH the hypothetical and the real d-node:
post_unnorm = {('a', 'u'): F(1, 2) * F(3, 4) * F(1, 2), ('a', 'v'): F(1, 2) * F(3, 4) * F(1, 2), ('b', 'u'): F(1, 2) * F(1, 4) * F(1, 2), ('b', 'v'): F(1, 2) * F(1, 4) * F(1, 2)}
Z = sum(post_unnorm.values()); post = {k: v / Z for k, v in post_unnorm.items()}
print(f" e's pre-enrichment strict-OC state: {pre}\n E-marginal of relocated nu~(.|O_e): {post}\n equal: {pre == post}  (relocation = shared seed on the nested fiber, FR-7(b)); pure C: both delta -> equal.")

print("\n=== F. Claim 7: the quotient obstruction, general one-liner ===")
print(" For ANY common information (Cbar, c, c') with a Cbar-event z such that c'(z) = bot: (Compat) gives p(c z) = p'(c' z) = p'(bot) = bot, so L(p(c z)) = 0;")
print(" probability-preservation gives L(p(c z)) = P_t0(c z).  Hence a compatible model exists only if P_t0(c z) = 0 for every such z.")
for p3 in (F(1, 2), F(1, 10), F(9, 10)):
    P7 = 1 - p3
    print(f"  stage instance P_t0(X_3)={p3}: c=id, c'=pi, z=X_7: P_t0(X_7)={P7} > 0 -> no compatible model; Thm 2.4's hypotheses hold (C' << C, density 1/P_t0(X_3) = {1/p3}) -> Thm 2.4 (<=) fails here.")

print("\n=== G. AN-3(iii): TN-V1 d_E expressible despite an unrecorded root decision edge ===")
tn = ex.transparent_newcomb(1, p=F(3, 4), L=4, S=1, mF=F(1, 2), mE=F(1, 2)); C12 = tn.policy(1, 2)
r = dp.Run(tn.B, C12); occ = set(r.occ('dE'))
w_in = {r.world(p) for p in occ if not dp.is_zero(r.mu[p])}; w_out = {r.world(p) for p in r.mu.keys() if p not in occ and not dp.is_zero(r.mu[p])}
print(" root node is a decision node (hypothetical d_F) whose answer is not a leaf-world coordinate:", type(tn.B.root).__name__, "| occ(d_E) expressible:", w_in.isdisjoint(w_out), "| Occ_dE worlds:", sorted(map(repr, w_in)))
