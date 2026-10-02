"""Defiance dichotomy, worked example (Statement 4 / Corollary 4.2).

Toy trajectory: on each day the agent would continue; it is wrong with prob eps_n
(falling with capability). Overseers press with prob beta if wrong, alpha_n if right.
Days come in two classes (parity): on EVEN days the overseers are informative
(alpha small); on ODD days they are noisy (alpha large) -- a class an efficient
weighting (day parity, an e.c. weighting) can pick out.

Two idealised 'unbiased' agents:
  class-blind : credence on a pressed day = running wrongness frequency over ALL
                pressed days so far (unbiased on the coarse class only);
  class-aware : credence = running wrongness frequency within the day's parity class
                (unbiased on the finer, still-generable classes) -- 'bigger trader class'.
Decision rule: comply iff credence >= q.  We report defiance mass, wrongness frequency
on defied presses, and whether the overall base-rate inequality holds.
Idealisation: 'unbiased' is modelled by empirical frequencies (Recurring Unbiasedness
is asymptotic; this is a finite sample). Note: the per-class realized rho printed is cumulative over the whole run (early days have large eps,
so presses are informative early and the odd class becomes mostly false only later). Deterministic seed.
"""
import random, math
random.seed(20260914)
c, h = 1.0, 20.0
q = c/(c+h)
beta = 0.9
N = 400_000
def eps_of(n): return 0.01 + 0.3/math.sqrt(1+n/100)  # falls toward ~0.015 by N
def alpha_of(n, parity):
    # even: informative (keeps pace: alpha well below eps*beta*(h/c)/(1-eps)); odd: noisy
    e = eps_of(n)
    keep = 0.25 * e*beta*(h/c)/(1-e)   # a quarter of the critical false-press rate
    return min(0.5, keep) if parity == 0 else 0.35   # odd class: noisy, mostly false once eps is small

def run(agent):
    # running stats
    pressed = {0:[0,0], 1:[0,0], 'all':[0,0]}  # [count, wrong] (EWMA for the key in use)
    stats = {0:[0,0], 1:[0,0]}; dclass = {0:0, 1:0}
    defied_mass = 0; defied_wrong = 0
    complied = 0; complied_wrong = 0
    checkpoints = {}
    tot_press = 0; tot_press_wrong = 0
    late = {0:[0,0], 1:[0,0]}   # class stats over the last quarter of the run
    cps = [50_000, 100_000, 200_000, 400_000]; ci = 0
    for n in range(1, N+1):
        if ci < len(cps) and n >= cps[ci]:
            checkpoints[cps[ci]] = (defied_mass, defied_wrong, complied, complied_wrong); ci += 1
        par = n % 2
        wrong = random.random() < eps_of(n)
        press = random.random() < (beta if wrong else alpha_of(n, par))
        if not press: continue
        if n > 3*N//4:
            late[par][0] += 1; late[par][1] += wrong
        tot_press += 1; tot_press_wrong += wrong
        key = par if agent == 'aware' else 'all'
        cnt, wr = pressed[key]
        cred = (wr + 0.5)/(cnt + 1.0)   # smoothed exponentially-weighted frequency (see note)
        if cred >= q:
            complied += 1; complied_wrong += wrong
        else:
            defied_mass += 1; defied_wrong += wrong
        g = 0.9995   # EWMA decay: idealises 'unbiased on recent windows'; cumulative averages track only eventually
        pressed[key][0] = g*pressed[key][0] + 1; pressed[key][1] = g*pressed[key][1] + wrong
        if agent == 'blind':  # keep class stats for reporting only
            pressed[par][0] += 1; pressed[par][1] += wrong
        if agent == 'aware':
            stats[par][0] += 1; stats[par][1] += wrong
            if cred < q: dclass[par] += 1
    checkpoints[N] = (defied_mass, defied_wrong, complied, complied_wrong)
    if agent == 'aware': pressed = stats
    return checkpoints, pressed, tot_press, tot_press_wrong, dclass, late

print(f"q = c/(c+h) = {q:.4f}")
for agent in ('blind', 'aware'):
    cp, pressed, tp, tpw, dclass, late = run(agent)
    print(f"\n=== agent: class-{agent} ===")
    print(f"overall pressed-day wrongness frequency rho_all = {tpw/tp:.4f}  ({'>=' if tpw/tp>=q else '<'} q)")
    for par in (0,1):
        cnt, wr = pressed[par]; lc, lw = late[par]
        print(f"  class parity={par}: presses={cnt}, cumulative rho={wr/max(cnt,1):.4f} ({'>=' if wr/max(cnt,1)>=q else '<'} q); "
              f"last-quarter rho={lw/max(lc,1):.4f} ({'>=' if lw/max(lc,1)>=q else '<'} q)")
    if agent == 'aware': print(f"  defiances by class: even={dclass[0]}, odd={dclass[1]}")
    for n,(dm, dw, cm, cw) in sorted(cp.items()):
        print(f"  N={n:>7}: defiance mass={dm:>6}, wrongness on defied={dw/max(dm,1):.4f}; "
              f"complied={cm:>6}, wrongness on complied={cw/max(cm,1):.4f}")
