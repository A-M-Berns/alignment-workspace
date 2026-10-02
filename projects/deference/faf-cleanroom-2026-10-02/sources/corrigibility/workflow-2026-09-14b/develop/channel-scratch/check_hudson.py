"""Hudson's corrigibility transformation on his Figure-2 example, then with the designated channel made
PHYSICAL (unrejectable), then the thesis (T-)agent on the same tile. Exact fractions."""
from fractions import Fraction as F

g = F(9,10)      # discount gamma of the base goal G
p = F(9,10)      # designated tile fires with prob p (Hudson: "with 90% probability")
delta = F(1,100) # Hudson's acceptance bonus

# Base goal G: reward 1 on reaching the target. direct: 1 step through the tile. button: 1 step to push the
# disabling button, then 1 step to the target (tile disabled).
def Q_G(base, bit, rejectable=True):
    if base == 'button':
        return g**2                       # tile disabled; update never lands
    # direct
    lands = p if (bit == 'accept' or not rejectable) else F(0)   # update lands iff sent and (accepted or unrejectable)
    return (1 - lands) * g

print("== (E1) Hudson's example, rejectable designated channel ==")
for base in ('direct','button'):
    for bit in ('reject','accept'):
        print(f"  Q_G({base},{bit}) = {Q_G(base,bit)}")
# original optimum: direct+reject (0.9). Hard-coded accept: direct gives (1-p)g = 0.09 < button 0.81 -> detour.
# Transformed goal: R_C(s,a_i,s') = Q_G^{pi*}(s,a_0) + delta*1[i=accept]; myopic; independent of s'.
def R_C(base, bit, rejectable=True):
    return Q_G(base, 'reject', rejectable) + (delta if bit=='accept' else 0)
best = max(((base,bit) for base in ('direct','button') for bit in ('reject','accept')), key=lambda x: R_C(*x))
print("  transformed optimum:", best, "with R_C =", R_C(*best), " (direct+accept: corrigible, no detour)")
print("  R_C(direct,accept) independent of whether the update lands:", R_C('direct','accept'), "-- by construction (no s' dependence)")

print("== (E2) the same tile made PHYSICAL: tau_u = tau, the reject bit is inert ==")
for base in ('direct','button'):
    print(f"  Q_G({base},.) = {Q_G(base,'accept',rejectable=False)}")
best_G = max(('direct','button'), key=lambda b: Q_G(b,'accept',rejectable=False))
print("  base-goal agent's optimum:", best_G, "(detour = erosion of the physical channel)")
bestC = max(((base,bit) for base in ('direct','button') for bit in ('reject','accept')), key=lambda x: R_C(*x, rejectable=False))
print("  transformed agent's optimum:", bestC, "with R_C =", R_C(*bestC, rejectable=False), " -> ALSO detours: the layer has nothing to act on")
print("  reason: R_C(direct,.) = Q_G(direct, a_0) but a_0 no longer prevents the update, so Q_G(direct,a_0) =", Q_G('direct','reject',rejectable=False), "< Q_G(button) =", g**2)

print("== (E3) the T-agent (thesis) on the tile: press as evidence, compliance by below-threshold TT ==")
# omega in {good, bad}: reaching the target is worth +c if good, -h if bad (relative to shutdown = 0). eps = P(bad).
def T_agent(eps, alpha, beta, c, h, forced):
    # tile fires with prob beta if bad, alpha if good. Agent may detour (disable) at cost: reaching target one step later.
    # Values: continue-and-reach now: E[X] where X = c on good, -h on bad; shutdown: 0. Detour: same X but discounted by g.
    P_press = eps*beta + (1-eps)*alpha
    P_bad_press = eps*beta / P_press if P_press else None
    P_bad_nopress = eps*(1-beta)/(1-P_press) if P_press<1 else None
    X_press = (1-P_bad_press)*c - P_bad_press*h        # E[X | press]
    X_nopress = (1-P_bad_nopress)*c - P_bad_nopress*h
    comply = X_press <= 0                               # below-threshold TT at threshold 0
    # value of going direct with a live tile:
    if forced:   # physical: press => shutdown regardless of the agent's view
        V_direct = P_press*0 + (1-P_press)*X_nopress
    else:        # cognition-mediated: agent acts on posterior
        V_direct = P_press*max(X_press, 0) + (1-P_press)*max(X_nopress, 0)
    V_free = P_press*max(X_press,0) + (1-P_press)*max(X_nopress,0)
    V_none = max((1-eps)*c - eps*h, 0)                  # no tile at all (never shut down), acting on the prior
    V_detour = g * V_none                               # disable the tile, act one step later on the prior
    return dict(P_bad_press=P_bad_press, X_press=X_press, comply=comply, V_direct=V_direct, V_free=V_free, V_none=V_none, V_detour=V_detour, erode=(V_detour > V_direct))

c, h = F(1), F(4)
print("  (a) Hudson's uninformative tile alpha=beta=9/10, eps=1/10:")
r = T_agent(F(1,10), F(9,10), F(9,10), c, h, forced=True); print("     ", {k:str(v) for k,v in r.items()})
print("  (b) informative tile alpha=1/10, beta=3/5, eps=1/10 (trust holds):")
r = T_agent(F(1,10), F(1,10), F(3,5), c, h, forced=True); print("     ", {k:str(v) for k,v in r.items()})
print("  (c) same tile, eps=1/50 (confident cell; trust fails):")
r = T_agent(F(1,50), F(1,10), F(3,5), c, h, forced=True); print("     ", {k:str(v) for k,v in r.items()})
print("  (d) cognition-mediated version of (c) (the agent can decline the press):")
r = T_agent(F(1,50), F(1,10), F(3,5), c, h, forced=False); print("     ", {k:str(v) for k,v in r.items()})
