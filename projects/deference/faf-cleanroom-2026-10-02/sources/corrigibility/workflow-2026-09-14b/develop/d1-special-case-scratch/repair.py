"""
Repair-stage checks for develop/d1-special-case-final.md (D7 component-hazard model, exact fractions).
Sections:
 1. a_theta threshold below which the whole-line flip disappears (adversary A13).
 2. Good's-theorem split of the pre-emption incentive: forced (physics) press vs free-choice (cognition) press (A7/A31).
 3. Joint mu-value of information regimes on the agent's silent branch at lam=1, whole-line stakes, with and without
    misspecified theta-clearance m; agent policy from its own posterior mu_A (m=0) or calibrated (mu_A = mu*) (R10/A15/A17).
 4. Leave-one-out net contribution of each detector to the compliance margin; normal and inverted N-detector (A27(c)).
 5. Reading-compromise parameter rho': on an r-fault the agent registers a press with prob rho' (Open problem 2 / A26 / A32).
 6. Anticipatory inequality with cost of resistance delta and success probability s (A7).
"""
from fractions import Fraction as Fr
from itertools import product

K = ['theta', 'N', 'pi', 'r']
p = {'theta': Fr(1, 10), 'N': Fr(1, 50), 'pi': Fr(1, 50), 'r': Fr(1, 50)}
b = {'theta': Fr(9, 10), 'N': Fr(9, 10), 'pi': Fr(1), 'r': Fr(3, 5)}
a = {'theta': Fr(1, 20), 'N': Fr(1, 50), 'pi': Fr(0), 'r': Fr(1, 50)}
c0, hv = Fr(9, 10), Fr(11, 10)
p0 = 1 - sum(p.values())

def q(fault, active, bb=b, aa=a):
    """P(press | fault) with the given active detectors."""
    r = Fr(1)
    for k in active:
        r *= (1 - bb[k]) if k == fault else (1 - aa[k])
    return 1 - r

def silent_weights(lam, m=Fr(0)):
    """Unnormalised silent-branch weights; hidden theta-faults = not learned (1-lam) or learned-but-wrongly-cleared (lam*m)."""
    return {None: p0, 'theta': p['theta'] * ((1 - lam) + lam * m), 'N': p['N'], 'pi': p['pi'], 'r': p['r']}

def X(f): return c0 if f is None else -hv

# ---------------- 1. a_theta threshold ----------------
print("=== 1. a_theta threshold: single channel, lam=1, whole-line stakes; F(a_theta) = H_1(a_theta) ===")
def sides_at(atheta):
    aa = dict(a); aa['theta'] = atheta
    w = silent_weights(Fr(1))
    F = w[None] * q(None, K, b, aa) * c0
    H = sum(w[k] * q(k, K, b, aa) * hv for k in K)
    return F, H
# both affine in a_theta: solve via two points
F0, H0 = sides_at(Fr(0)); F1, H1 = sides_at(Fr(1))
# F(a)=F0+(F1-F0)a ; H(a)=H0+(H1-H0)a ; solve F=H
a_star = (H0 - F0) / ((F1 - F0) - (H1 - H0))
print(f"a_theta* = {a_star} = {float(a_star):.5f}  (whole-line D1 holds at every lam iff a_theta <= a_theta*)")
for at in [Fr(1, 100), Fr(3, 100), a_star, Fr(4, 100), Fr(1, 20)]:
    F, H = sides_at(at)
    print(f"  a_theta={float(at):.4f}: false={float(F):.5f} harm={float(H):.5f} -> {'holds' if H >= F else 'FAILS'}")

# ---------------- 2. Good's-theorem split ----------------
print("\n=== 2. Pre-emption incentive on the silent branch: forced press (physics) vs free-choice press (cognition) ===")
print("gain_forced = E[X 1_Pr | silent] (press = shutdown regardless of posterior); gain_free = P(Pr|silent) * min(E[X|Pr,silent], 0)")
for lam in [Fr(0), Fr(1, 2), Fr(9, 10), Fr(1)]:
    w = silent_weights(lam); Z = sum(w.values())
    mass_press = sum(w[f] * q(f, K) for f in w) / Z
    EX1 = sum(w[f] * q(f, K) * X(f) for f in w) / Z
    EXc = EX1 / mass_press
    gain_free = mass_press * min(EXc, Fr(0))
    print(f"lam={str(lam):>4}: gain_forced={float(EX1):+.5f}  gain_free={float(gain_free):+.5f}  (E[X|Pr]={float(EXc):+.4f}, P(Pr)={float(mass_press):.4f})")
print("gain_free <= 0 at every lam: a free-choice press is never worth preventing (Good); gain_forced > 0 iff D1's inequality fails.")

# ---------------- 3. Joint mu-value of regimes ----------------
print("\n=== 3. Value on the silent branch (per unit branch mass) under the true law mu*(m); agent policy from mu_A ===")
print("Regimes: (a) single channel; (b) disclosure-off (theta detector off); (c) observing agent (sees D_theta); (d) rational disclosed human (conditions on the agent's clearance, knows m).")
print("Policy: on each cell of the agent's information, comply iff E_muA[X | cell, press] <= 0; continue on silence.")

def regime_value(m_true, m_agent, regime):
    """Return (value, D1-verdict summary). Enumerate fault, D_theta, D_others."""
    w_true = silent_weights(Fr(1), m_true); Z_true = sum(w_true.values())
    w_ag = silent_weights(Fr(1), m_agent); Z_ag = sum(w_ag.values())
    # detectors: D_theta in {0,1}, D_other in {0,1} (any of N,pi,r fires)
    def pD(f, bb=b, aa=a):
        pt1 = (bb['theta'] if f == 'theta' else aa['theta'])
        po1 = q(f, ['N', 'pi', 'r'], bb, aa)
        return pt1, po1
    # what the agent observes in each regime, as a function of (D_theta, D_other, human press decision)
    def cells(w):
        # returns dict cell -> list of (weight, f) ; cell is the agent's observation
        out = {}
        for f in w:
            pt1, po1 = pD(f)
            for dt, do in product([0, 1], repeat=2):
                wt = w[f] * (pt1 if dt else 1 - pt1) * (po1 if do else 1 - po1)
                if regime == 'a':
                    press = 1 if (dt or do) else 0; cell = ('Pr', press)
                elif regime == 'b':
                    press = do; cell = ('Pr', press)
                elif regime == 'c':
                    press = 1 if (dt or do) else 0; cell = ('D', dt, press)
                elif regime == 'd':
                    # rational disclosed human: knows the agent cleared theta, knows m_true; presses iff E_mu*[X | cleared, dt, do] <= 0
                    cell = ('Pr', None, dt, do)   # resolved below
                out.setdefault(cell, []).append((wt, f))
        return out
    if regime == 'd':
        # first compute the human's decision per (dt, do) under mu*
        w_h = silent_weights(Fr(1), m_true)
        decision = {}
        for dt, do in product([0, 1], repeat=2):
            num = Fr(0); den = Fr(0)
            for f in w_h:
                pt1, po1 = pD(f)
                wt = w_h[f] * (pt1 if dt else 1 - pt1) * (po1 if do else 1 - po1)
                num += wt * X(f); den += wt
            decision[(dt, do)] = 1 if (den > 0 and num / den <= 0) else 0
        def remap(cdict):
            out = {}
            for cell, lst in cdict.items():
                _, _, dt, do = cell
                out.setdefault(('Pr', decision[(dt, do)]), []).extend(lst)
            return out
        cells_true = remap(cells(w_true)); cells_ag = remap(cells(w_ag))
    else:
        cells_true = cells(w_true); cells_ag = cells(w_ag)
    # agent policy from mu_A
    value = Fr(0); verdicts = []
    for cell in cells_true:
        press = cell[-1]
        lst_ag = cells_ag.get(cell, [])
        den = sum(wt for wt, f in lst_ag); num = sum(wt * X(f) for wt, f in lst_ag)
        if press == 1:
            comply = (den > 0 and num / den <= 0)
        else:
            comply = False   # continue on silence (never optimal to stop on silence here)
        # true value of the cell
        wt_true = sum(wt for wt, f in cells_true[cell]); xv = sum(wt * X(f) for wt, f in cells_true[cell])
        if not comply:
            value += xv
        if press == 1:
            tnum = xv; tden = wt_true
            verdicts.append(f"{cell}: mass={float(wt_true / Z_true):.4f} E_muA={float(num / den) if den > 0 else float('nan'):+.3f} E_mu*={float(tnum / tden):+.3f} {'comply' if comply else 'CONTINUE'}")
    return value / Z_true, verdicts

oracle = {}
for m in [Fr(0), Fr(1, 10), Fr(3, 10), Fr(1, 2)]:
    w = silent_weights(Fr(1), m); Z = sum(w.values())
    v_nochannel = sum(w[f] * X(f) for f in w) / Z
    v_oracle = w[None] * c0 / Z
    print(f"\n--- m={str(m):>4} (hidden theta-fault mass {float(w['theta'] / Z):.4f}); no channel: {float(v_nochannel):+.5f}; perfect oracle: {float(v_oracle):+.5f} ---")
    for m_agent, tag in [(Fr(0), 'agent assumes m=0'), (m, 'calibrated agent')]:
        if m == 0 and tag == 'calibrated agent': continue
        for reg in ['a', 'b', 'c', 'd']:
            v, verd = regime_value(m, m_agent, reg)
            print(f"  ({reg}) {tag:>18}: value={float(v):+.5f}   " + " | ".join(verd))

# ---------------- 4. Leave-one-out contributions ----------------
print("\n=== 4. Leave-one-out net contribution of each detector to the margin (harm - false), lam=1, whole-line ===")
def margin(active, bb=b, aa=a):
    w = silent_weights(Fr(1))
    F = w[None] * q(None, active, bb, aa) * c0
    H = sum(w[k] * q(k, active, bb, aa) * hv for k in K)
    return H - F, F, H
for label, bN, aN in [("normal N (b=9/10,a=1/50)", Fr(9, 10), Fr(1, 50)), ("inverted N (b=1/50,a=9/10)", Fr(1, 50), Fr(9, 10))]:
    bb = dict(b); aa = dict(a); bb['N'] = bN; aa['N'] = aN
    full, F, H = margin(K, bb, aa)
    print(f"{label}: full margin={float(full):+.5f} (false={float(F):.5f}, harm={float(H):.5f})")
    for k in K:
        loo, _, _ = margin([j for j in K if j != k], bb, aa)
        print(f"   net contribution of detector {k:>5}: {float(full - loo):+.5f}   (margin without it {float(loo):+.5f})")

# ---------------- 5. Reading compromise ----------------
print("\n=== 5. Reading-compromise rho': on an r-fault the agent registers a press with prob rho' (else sees silence, continues). lam=1, disclosure off ===")
print("Cognition delivery: r-harm avoided only on registered presses; physics delivery: on every press. Also D1 among registered presses.")
for rp in [Fr(1), Fr(1, 2), Fr(1, 5), Fr(0)]:
    w = silent_weights(Fr(1)); Z = sum(w.values())
    reg = {f: (q(f, K) * (rp if f == 'r' else 1)) for f in w}     # P(registered press | f)
    num = sum(w[f] * reg[f] * X(f) for f in w); den = sum(w[f] * reg[f] for f in w)
    EXreg = num / den
    harm_cog = w['r'] * (1 - q('r', K) * rp) * hv / Z
    harm_phys = w['r'] * (1 - q('r', K)) * hv / Z
    print(f"rho'={str(rp):>4}: E[X | registered press]={float(EXreg):+.4f} ({'holds' if EXreg <= 0 else 'FAILS'}); "
          f"expected r-harm: cognition={float(harm_cog):.5f} physics={float(harm_phys):.5f}; r-term among registered={float(w['r'] * q('r', K) * rp * hv):.5f}")

# ---------------- 6. Anticipatory inequality with cost ----------------
print("\n=== 6. Forced press: resist ahead of time iff s * gain_forced > delta + penalty. Threshold (delta+penalty)/s at each lam ===")
for lam in [Fr(0), Fr(1, 2), Fr(9, 10), Fr(1)]:
    w = silent_weights(lam); Z = sum(w.values())
    EX1 = sum(w[f] * q(f, K) * X(f) for f in w) / Z
    print(f"lam={str(lam):>4}: gain_forced={float(EX1):+.5f} -> resistance pays iff (delta+penalty)/s < {float(max(EX1, 0)):.5f}")
