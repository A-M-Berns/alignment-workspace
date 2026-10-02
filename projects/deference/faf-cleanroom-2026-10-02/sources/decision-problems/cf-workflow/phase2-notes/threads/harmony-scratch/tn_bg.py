"""tn_bg.py -- TN-V2 (p=3/4, L=4, S=1) as a bargaining game: (i) homogeneous translation (common X = beta on chance
profiles; U = V_B on pure profiles) and (ii) the 'updateful' translation (d_F conditions on full, d_E on empty --
own-profile event-conditioning, the only way to make the world-models profile-independent here).  Also the mugging."""
from fractions import Fraction as F
from itertools import product
from bargaining import BG, fmt_strat
import sys
sys.path.insert(0, '[scrubbed]')
import dp, examples as ex
from dp import Run, Procedure

tn = ex.transparent_newcomb(2, p=F(3,4), L=4, S=1)
V = {}; UF = {}; UE = {}
for x in (1,2):
    for y in (1,2):
        C = tn.policy(x, y); run = Run(tn.B, C)
        V[(x,y)] = run.value
        UF[(x,y)] = run.E_r(lambda li: tn.O_F(li.world))   # E[r | full] under this very profile
        UE[(x,y)] = run.E_r(lambda li: tn.O_E(li.world))
print("V =", {k: str(v) for k, v in V.items()}, "\nU_F (given full) =", {k: str(v) for k, v in UF.items()}, "\nU_E (given empty) =", {k: str(v) for k, v in UE.items()})
def thpe_outcomes(U, W):
    G = BG([[1,2],[1,2]], U, W)
    outs = set()
    for sigma in product(*G.S):
        if G.is_nash(sigma) and G.is_uniform_thpe(sigma)[0]:
            outs.add(G.outcome(sigma))
    return outs
Wh = {O: V[O] + F(k, 1000) for k, O in enumerate(V)}
print("homogeneous BG (U_F = U_E = V): uniform-THPE outcomes =", thpe_outcomes([V, V], Wh))
Wu = {O: UF[O] + UE[O] + F(k, 1000) for k, O in enumerate(V)}
print("updateful BG (U_F = E[r|full], U_E = E[r|empty]): uniform-THPE outcomes =", thpe_outcomes([UF, UE], Wu),
      "; Pareto-undominated outcomes:", [O for O in V if not BG([[1,2],[1,2]], [UF, UE], Wu).pareto_dominated(O)])
# mugging, one player
m = ex.mugging(1, x=1, y=2, q0=F(1,2))
Vm = {('pay',): dp.value(m.B, Procedure({m.d: 'pay'})), ('refuse',): dp.value(m.B, Procedure({m.d: 'refuse'}))}
Um = {('pay',): Run(m.B, Procedure({m.d: 'pay'})).E_r(lambda li: m.O_T(li.world)), ('refuse',): Run(m.B, Procedure({m.d: 'refuse'})).E_r(lambda li: m.O_T(li.world))}
print("mugging: V =", Vm, " E[r|T] =", Um)
for lab, U in (("homogeneous", Vm), ("updateful (X = beta(.|T))", Um)):
    W = {O: U[O] + F(k, 1000) for k, O in enumerate(U)}
    G = BG([['pay','refuse']], [U], W)
    outs = {G.outcome((s,)) for s in G.S[0] if G.is_nash((s,)) and G.is_uniform_thpe((s,))[0]}
    print(f"  mugging BG {lab}: THPE outcomes = {outs}")
