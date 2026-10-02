"""FP item 5: the audit 's ~ s°(.|occ(d))' — grade, referent, TN-V1/V2 contrast, Prop 1'."""
from common import *

print("=== A. Mugging: prior on the lifted algebra (leaves), conditioned on occ(d) ===")
m = ex.mugging(1)
Cm = Procedure({m.d: {'pay': m.q0, 'refuse': 1 - m.q0}})
run = dp.Run(m.B, Cm)
# s° on 2^Leaves: P = mu (Def 11 prior calibration on the lift), pushed down along lambda gives nu
P_leaf = run.mu
occ = lambda p: run.leaf(p).count('d') > 0
s0_cond = P_leaf.condition(occ).map(lambda p: run.world(p))
show("lambda_*(P_{s°}(.|occ(d)))", s0_cond)
s_oc = dp.calibrated_state(m.B, Cm, m.d, 'strict')
s_ssc = dp.calibrated_state(m.B, Cm, m.d, 'per-run')
show("audit of the tails-certain OC state: pass?", s_oc.P == s0_cond)
show("audit of the per-run SSC state: pass?", s_ssc.P == s0_cond)
show("Prop 1': s°(.|occ) == per-run SSC statistic (Def 13)?", s_ssc.P == s0_cond)
show("  and s°(.|occ, O_T) == strict-OC statistic (Def 8)?", P_leaf.condition(lambda p: occ(p) and run.world(p)['coin'] == 'T').map(lambda p: run.world(p)) == s_oc.P)

print("\n=== B. Transparent Newcomb: the audit passes the empty box in V1 and fails it in V2 ===")
for v in [1, 2]:
    tn = ex.transparent_newcomb(v, p=F(3, 4), L=4, S=1)
    print(tn.B.show())
    # V-optimal policies from v2 §7.2 at p=3/4, L=4, S=1: V1 -> (1,2); V2 -> (1,1)
    pol = {1: ('large', 'both'), 2: ('large', 'large')}[v]
    C = Procedure({tn.dF: pol[0], tn.dE: pol[1]})
    for d in [tn.dF, tn.dE]:
        run = dp.Run(tn.B, C)
        occ_mass = run.mu_occ(d)
        s_strict = dp.calibrated_state(tn.B, C, d, 'strict')
        s_run = dp.calibrated_state(tn.B, C, d, 'per-run')
        show(f"V{v}, {d.name}: mu(occ)", occ_mass)
        show(f"V{v}, {d.name}: OC state P", None if s_strict is None else s_strict.P)
        show(f"V{v}, {d.name}: s°(.|occ) = per-run SSC P", None if s_run is None else s_run.P)
        if s_strict is not None and s_run is not None:
            show(f"V{v}, {d.name}: audit passes the OC-calibrated state?", s_strict.P == s_run.P)
