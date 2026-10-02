"""rp_reverify.py -- repair agent's THIRD, independent re-verification for the harmony thread (2026-09-02).
Nothing imported from threads/harmony-scratch or adversary/harmony-scratch.  Exact Fractions throughout.
Sections:
  A  HA-4   SC Thm 11.1 counterexample (Nash at eps=0; lexicographic (M,T); perturbed payoffs; W Pareto-consistent; 72 vs 68; -4 decomposition)
  B  HA-5(iii)/HA-14(i)  reviewer's no-safe-batna game: uniform-THPE outcomes = {argmax_W M}; dominance lemma; random 2x2 and 3x2 games
  C  HA-15  two-prior mugging as SC's game: no (pay,pay) profile is Nash; THPE outcomes implement refuse for every W tried; linearity identity
  D  HA-12(b) relocated mugging root: strict / limit / prior senses collapse A^+ to the played action (toolkit, TRUSTED functions), masked and tremble senses do not; by-hand check
  E  HA-8(d) coverage: coupled vs decoupled mugging (event-grand conflict-freeness vs V-optimality)
  F  HA-10  grand coalition as one player: harmonious outcomes {ac, bd} vs singleton players {bd}
  G  HA-8/HA-9 Definition-23 tables on TN-V2 (both modes) and the three-point family table (own formulas)
  H  sanity: Stag Hunt 43/0 and 337/4; FR-12 three optima under each W order; two-point mugging B_1' (identity's Open 4)
"""
from fractions import Fraction as F
from itertools import product, combinations, chain
import random, sys, time

def subsets(xs):
    xs = list(xs)
    return chain.from_iterable(combinations(xs, r) for r in range(len(xs) + 1))

class BG:
    """SC Def 10.2 bargaining game, n = 2, exact arithmetic; W injective."""
    def __init__(self, A1, A2, U1, U2, W):
        self.outs = [(a, b) for a in A1 for b in A2]
        assert len(set(W[o] for o in self.outs)) == len(self.outs), "W not injective"
        self.U = (U1, U2); self.W = W
        self.S = [[(b, frozenset(acc)) for b in A for acc in subsets(self.outs)] for A in (A1, A2)]
        self.K = [len(s) for s in self.S]
        self.out = {}
        for s1 in self.S[0]:
            for s2 in self.S[1]:
                inter = s1[1] & s2[1]
                self.out[(s1, s2)] = max(inter, key=lambda o: W[o]) if inter else (s1[0], s2[0])
    def pay(self, i, prof): return self.U[i][self.out[prof]]
    def prof_with(self, i, s, prof): return (s, prof[1]) if i == 0 else (prof[0], s)
    def nash(self, prof):
        return all(self.pay(i, self.prof_with(i, s, prof)) <= self.pay(i, prof) for i in range(2) for s in self.S[i])
    def MT(self, i, s, prof):
        """first-order payoff against the opponent's pure strategy, and total against all K_{-i} opponent strategies
        (payoff against the uniformly eps-trembled opponent is M + eps*(T - K*M))."""
        j = 1 - i
        M = self.U[i][self.out[self.prof_with(i, s, prof)]]
        T = sum(self.U[i][self.out[(s, t) if i == 0 else (t, s)]] for t in self.S[j])
        return (M, T)
    def uniform_thpe(self, prof):
        return all(self.MT(i, s, prof) <= self.MT(i, prof[i], prof) for i in range(2) for s in self.S[i])
    def perturbed(self, i, s, prof, eps):
        j = 1 - i; tot = F(0)
        for t in self.S[j]:
            w = 1 - (self.K[j] - 1) * eps if t == prof[j] else eps
            tot += w * self.U[i][self.out[(s, t) if i == 0 else (t, s)]]
        return tot
    def dominated(self, o, strict=False):
        res = []
        for o2 in self.outs:
            if o2 == o: continue
            ge = all(self.U[i][o2] >= self.U[i][o] for i in range(2))
            gt = [self.U[i][o2] > self.U[i][o] for i in range(2)]
            if ge and (all(gt) if strict else any(gt)): res.append(o2)
        return res
    def W_pareto_consistent(self):
        return all(self.W[o2] > self.W[o] for o in self.outs for o2 in self.dominated(o))
    def thpe_table(self):
        tab = {}
        for prof in product(*self.S):
            if self.nash(prof):
                o = self.out[prof]; tab.setdefault(o, [0, 0]); tab[o][0] += 1
                if self.uniform_thpe(prof): tab[o][1] += 1
        return tab
    def thpe_outcomes(self):
        return sorted(o for o, v in self.thpe_table().items() if v[1] > 0)

def s(o): return ''.join(map(str, o))
def hdr(t): print("\n" + "=" * 96 + f"\n{t}\n" + "=" * 96)
def rank_W(order):  # W injective from an explicit order, first = largest
    return {o: F(len(order) - k) for k, o in enumerate(order)}

# ------------------------------------------------------------------------------------------------ A
hdr("A. HA-4: SC Thm 11.1 counterexample, third independent recomputation")
A1, A2 = ['a', 'b'], ['c', 'd']
outs = [(p, q) for p in A1 for q in A2]
U1 = dict(zip(outs, map(F, [3, 0, 2, 0]))); U2 = dict(zip(outs, map(F, [0, 0, 1, 3])))
W = {o: U1[o] + 2 * U2[o] + F(k, 1000) for k, o in enumerate(outs)}
G = BG(A1, A2, U1, U2, W)
print("W:", {s(o): str(W[o]) for o in outs}, "| injective+Pareto-consistent:", G.W_pareto_consistent())
star = (('a', frozenset({('a', 'c')})), ('d', frozenset({('b', 'd')})))
o_star = G.out[star]
print("sigma* = (a,{ac}),(d,{bd}); outcome", s(o_star), "U =", (str(U1[o_star]), str(U2[o_star])),
      "; strictly dominated by", [s(o) for o in G.dominated(o_star, strict=True)])
print("Nash at eps=0:", G.nash(star), "| lexicographic uniform-tremble test:", G.uniform_thpe(star))
for i in range(2):
    Ms = {s_: G.MT(i, s_, star) for s_ in G.S[i]}
    print(f"  player {i+1}: (M,T)(s*) = {Ms[star[i]]}; max M over 32 = {max(m for m, _ in Ms.values())}; max T = {max(t for _, t in Ms.values())}")
alt = (('a', frozenset({('a', 'c'), ('b', 'c')})), ('d', frozenset({('b', 'd'), ('b', 'c')})))
print("  SC deviation 'add bc': player1 (M,T) =", G.MT(0, alt[0], star), "player2 (M,T) =", G.MT(1, alt[1], star))
for eps in (F(1, 100), F(1, 1000), F(1, 10**6)):
    for i in range(2):
        v = G.perturbed(i, star[i], star, eps); best = max(G.perturbed(i, t, star, eps) for t in G.S[i])
        print(f"  eps={eps}: player {i+1} payoff(s*) = {v}, max over 32 pure = {best}, best response: {v == best}")
gain = mech_a = mech_b = F(0)
for t in G.S[1]:
    d = U1[G.out[(alt[0], t)]] - U1[G.out[(star[0], t)]]
    if d > 0: gain += d
    elif d < 0:
        if G.out[(star[0], t)] == ('a', 'c') and ('a', 'c') not in t[1]: mech_a += d   # no-deal ac (batna) lost to the deal bc
        else: mech_b += d                                                             # deal ac displaced by bc (welfare displacement)
print(f"  player 1 second-order decomposition: gain {gain}, mechanism (a) batna ac->bc {mech_a}, mechanism (b) welfare displacement {mech_b}, net {gain+mech_a+mech_b}")
tab = G.thpe_table()
print("  Nash / uniform-THPE counts per outcome:", {s(o): v for o, v in tab.items()},
      "| dominated outcomes reached by uniform-THPE profiles:", [s(o) for o, v in tab.items() if v[1] > 0 and G.dominated(o)])

# ------------------------------------------------------------------------------------------------ B
hdr("B. HA-5(iii)/HA-14(i): common payoff, two optima, no safe batna -> W selects (reviewer's Proposition S)")
V = dict(zip(outs, map(F, [1, 0, 0, 1])))
def safe_batnas(A1_, A2_, V_):
    mx = max(V_.values())
    return ([b for b in A1_ if all(V_[(b, c)] == mx for c in A2_)], [b for b in A2_ if all(V_[(a, b)] == mx for a in A1_)])
print("safe batnas:", safe_batnas(A1, A2, V))
for lab, order in (("bd > ac > ad > bc", [('b','d'),('a','c'),('a','d'),('b','c')]), ("ac > bd > ad > bc", [('a','c'),('b','d'),('a','d'),('b','c')])):
    Gb = BG(A1, A2, V, V, rank_W(order)); assert Gb.W_pareto_consistent()
    tb = Gb.thpe_table()
    print(f"  W: {lab}: Nash/uniform-THPE per outcome {{ {', '.join(s(o)+': '+str(v) for o, v in tb.items())} }} -> uniform-THPE outcomes {[s(o) for o in Gb.thpe_outcomes()]}")
    # dominance lemma for the W-max optimum: adding it weakly dominates profile-by-profile and is strict somewhere
    Wmax = order[0]
    for i in range(2):
        weak_all = True; strict_all = True
        for st in Gb.S[i]:
            if Wmax in st[1]: continue
            st2 = (st[0], st[1] | {Wmax}); weak = True; strict = False
            for t in Gb.S[1 - i]:
                p1 = (st, t) if i == 0 else (t, st); p2 = (st2, t) if i == 0 else (t, st2)
                d = Gb.U[i][Gb.out[p2]] - Gb.U[i][Gb.out[p1]]
                if d < 0: weak = False
                if d > 0: strict = True
            weak_all &= weak; strict_all &= strict
        print(f"     player {i+1}: adding {s(Wmax)} weakly dominates profile-by-profile: {weak_all}; strictly better at some opponent strategy, for every such strategy: {strict_all}")
random.seed(2026)
n_games = viol = nosafe = sharp = 0
for _ in range(200):
    Vr = {o: F(random.randint(0, 3)) for o in outs}
    order = sorted(outs, key=lambda o: (Vr[o], random.random()), reverse=True)
    Gr = BG(A1, A2, Vr, Vr, rank_W(order)); n_games += 1
    mx = max(Vr.values()); M = [o for o in outs if Vr[o] == mx]
    outsT = Gr.thpe_outcomes()
    if any(Vr[o] < mx for o in outsT): viol += 1
    sb = safe_batnas(A1, A2, Vr)
    if not sb[0] and not sb[1]:
        nosafe += 1
        if set(outsT) == {max(M, key=lambda o: Gr.W[o])}: sharp += 1
        else: print("   Proposition S FAILS on", {s(o): str(Vr[o]) for o in outs}, outsT)
print(f"  random 2x2 common-payoff games: {n_games}; non-optimal uniform-THPE outcomes: {viol}; no-safe-batna games: {nosafe}; of these THPE set == {{argmax_W M}}: {sharp}")
A1b, A2b = ['a', 'b', 'c'], ['x', 'y']; outs3 = [(p, q) for p in A1b for q in A2b]
random.seed(7); t0 = time.time(); n3 = viol3 = nosafe3 = sharp3 = 0
for _ in range(4):
    Vr = {o: F(random.randint(0, 2)) for o in outs3}
    order = sorted(outs3, key=lambda o: (Vr[o], random.random()), reverse=True)
    Gr = BG(A1b, A2b, Vr, Vr, rank_W(order)); n3 += 1
    mx = max(Vr.values()); M = [o for o in outs3 if Vr[o] == mx]; outsT = Gr.thpe_outcomes()
    if any(Vr[o] < mx for o in outsT): viol3 += 1
    sb = safe_batnas(A1b, A2b, Vr); tag = ""
    if not sb[0] and not sb[1]:
        nosafe3 += 1
        if set(outsT) == {max(M, key=lambda o: Gr.W[o])}: sharp3 += 1
        else: tag = " <-- Proposition S FAILS"
    print(f"   3x2: V={ {s(o): str(Vr[o]) for o in outs3} } optima={[s(o) for o in M]} safe={sb} THPE={[s(o) for o in outsT]}{tag}")
print(f"  random 3x2 games: {n3}; non-optimal THPE outcomes {viol3}; no-safe-batna games {nosafe3}; Proposition S holds in {sharp3}  [{time.time()-t0:.1f}s]")

# ------------------------------------------------------------------------------------------------ C
hdr("C. HA-15: two-prior mugging as SC's bargaining game (x=1, y=2, X1(H)=1/2, X2(H)=1/4; policy = pay iff both say pay)")
x, y, th = F(1), F(2), F(1, 4)
Ap = ['pay', 'refuse']; outs_p = [(p, q) for p in Ap for q in Ap]
def Uself(pH, o): return (pH * y - (1 - pH) * x) if o == ('pay', 'pay') else F(0)
Up1 = {o: Uself(F(1, 2), o) for o in outs_p}; Up2 = {o: Uself(th, o) for o in outs_p}
print("U1 =", {s(o): str(v) for o, v in Up1.items()}, " U2 =", {s(o): str(v) for o, v in Up2.items()})
for w1 in (F(1, 2), F(3, 4), F(9, 10), F(99, 100)):
    w2 = 1 - w1
    Wp = {o: w1 * Up1[o] + w2 * Up2[o] + F(k, 10**6) for k, o in enumerate(outs_p)}
    Gp = BG(Ap, Ap, Up1, Up2, Wp)
    mixH = w1 * F(1, 2) + w2 * th
    tb = Gp.thpe_table()
    print(f"  w1={w1}: W(pay,pay)={w1*Up1[('pay','pay')]+w2*Up2[('pay','pay')]} = UDT value under mixture prior P(H)={mixH}: {mixH*y-(1-mixH)*x};"
          f" W prefers {'PAY' if Wp[('pay','pay')] > Wp[('refuse','refuse')] else 'refuse'};"
          f" any Nash profile with outcome (pay,pay)? {any(Gp.nash(p) for p in product(*Gp.S) if Gp.out[p] == ('pay','pay'))};"
          f" uniform-THPE outcomes {[s(o) for o in Gp.thpe_outcomes()]} -> implemented policy {sorted(set('pay' if o == ('pay','pay') else 'refuse' for o in Gp.thpe_outcomes()))}")
print("  player 2's (refuse, {}) guarantees 0 against every player-1 strategy:",
      all(Gp.U[1][Gp.out[(t, ('refuse', frozenset()))]] == 0 for t in Gp.S[0]))

# ------------------------------------------------------------------------------------------------ D
hdr("D. HA-12(b): EDT at the relocated mugging root under strict / limit / prior / masked / tremble senses (toolkit + by hand)")
sys.path.insert(0, '[scrubbed]')
import dp, examples as ex
from dp import Procedure
rm = ex.relocated_mugging_direct(x=1, y=2); B, dhat = rm.B, rm.dhat
names = dhat.action_names
C_pay = Procedure({dhat: rm.A_pay}, name='pol=pay'); C_ref = Procedure({dhat: rm.A_ref}, name='pol=refuse')
print("V(pay) =", dp.value(B, C_pay), " V(refuse) =", dp.value(B, C_ref), " (optimum: pay)")
print("recording at d^ for both procedures:", dp.records(dp.Run(B, C_pay), dhat).ok, dp.records(dp.Run(B, C_ref), dhat).ok)
for C in (C_pay, C_ref):
    for sense in ('strict', 'limit', 'prior'):
        st = dp.calibrated_state(B, C, dhat, sense); B2 = dp.with_states(B, {dhat: st}); d2 = B2.point('^d')
        vals = dp.edt_values(d2)
        print(f"  C={C.name:<11} sense={sense:<6}: A^+={sorted(vals)}, act values={ {k: str(v) for k, v in vals.items()} }, EDT(d^)={dp.EDT(d2)}, T_EDT approves C: {dp.T_EDT(C, B2).ok}")
    for m in (F(1, 2), F(1, 4)):
        Cm = Procedure({dhat: {names[0]: m, names[1]: 1 - m}}, name=f'self-model m={m}')
        st = dp.calibrated_state(B, Cm, dhat, 'strict'); B2 = dp.with_states(B, {dhat: st}); d2 = B2.point('^d')
        vals = dp.edt_values(d2)
        print(f"  C={C.name:<11} masked (self-model P(pay)={m}): A^+={sorted(vals)}, act values={ {k: str(v) for k, v in vals.items()} }, EDT(d^)={dp.EDT(d2)}, T_EDT approves C: {dp.T_EDT(C, B2).ok}")
    print(f"  C={C.name:<11} tremble-EDT-consistent (Remark 3.12 concrete form): {dp.tremble_edt_consistent(B, C).consistent}")
print("  by hand: under deterministic C=refuse every leaf carries pol_d=refuse, so nu(pol=refuse)=1 and strict/prior calibration force P(pol=pay)=0 (Remark 3.6);"
      " limit: nu_{C^eps}(pol=pay) = eps/2 -> 0.  Hence A^+ = {refuse} in all three senses and EDT(d^) = refuse (Remark 3.9's collapse).")

# ------------------------------------------------------------------------------------------------ E
hdr("E. HA-8(d): coverage is sufficient, not necessary (coupled vs decoupled mugging, x=1, y=2)")
def mug(pay, coupled):
    if pay: return [(F(1, 2), True, -x), (F(1, 2), False, y if coupled else F(0))]   # (prob, satisfies O_T, r)
    return [(F(1, 2), True, F(0)), (F(1, 2), False, F(0))]
for coupled, lab in ((True, "coupled (Counterfactual Mugging)"), (False, "decoupled (heads payoff policy-independent)")):
    Vv = {a: sum(p * r for p, _, r in mug(a == 'pay', coupled)) for a in ('pay', 'refuse')}
    Ev = {a: sum(p * r for p, t, r in mug(a == 'pay', coupled) if t) / sum(p for p, t, _ in mug(a == 'pay', coupled) if t) for a in ('pay', 'refuse')}
    opt = {a for a in Vv if Vv[a] == max(Vv.values())}; evg = {a for a in Ev if Ev[a] == max(Ev.values())}
    print(f"  {lab}: V={ {a: str(v) for a, v in Vv.items()} }, E[r|T]={ {a: str(v) for a, v in Ev.items()} }; optimal={opt}; event-grand conflict-free={evg}; coverage fails (heads-run satisfies no observation); equal: {opt == evg}")

# ------------------------------------------------------------------------------------------------ F
hdr("F. HA-10: the grand coalition as ONE player on the no-safe-batna game (V(ac)=V(bd)=1, W: bd > ac)")
Wg = rank_W([('b','d'),('a','c'),('a','d'),('b','c')])
one = set()
for b in outs:
    for acc in subsets(outs):
        acc = frozenset(acc); o = max(acc, key=lambda z: Wg[z]) if acc else b
        if V[o] == 1: one.add(o)          # one player: perturbed-game Nash = constrained best response; limits = best responses; every best response is optimal
print("  harmonious outcomes with one player owning the whole profile:", sorted(s(o) for o in one), " vs singleton players (section B): ['bd']")

# ------------------------------------------------------------------------------------------------ G
hdr("G. Definition-23 tables: TN-V2 (p=3/4, L=4, S=1) in occurrence and event mode; three-point family table")
p, L, S = F(3, 4), F(4), F(1)
def tn_leaves(x_, y_):
    b = p if (x_, y_) == (1, 1) else 1 - p
    return [(b, 1, L + (S if x_ == 2 else 0)), (1 - b, 0, S if y_ == 2 else 0)]   # (prob, fill, r)
pols = [(a, b) for a in (1, 2) for b in (1, 2)]
def Vtn(pol): return sum(pr * r for pr, _, r in tn_leaves(*pol))
def cond(pol, pred):
    ls = [(pr, r) for pr, f, r in tn_leaves(*pol) if pred(f)]; m = sum(pr for pr, _ in ls)
    return None if m == 0 else sum(pr * r for pr, r in ls) / m
OBS = {'F': lambda f: f == 1, 'E': lambda f: f == 0}; idx = {'F': 0, 'E': 1}
def conflict_free(family, mode):
    res = []
    for pol in pols:
        ok = True
        for D in family:
            pred = (lambda f: True) if mode == 'occ' else (lambda f, D=D: any(OBS[d](f) for d in D))   # occ(d_F)=occ(d_E)=all leaves in TN-V2
            base = cond(pol, pred)
            if base is None: continue
            for combo in product((1, 2), repeat=len(D)):
                q = list(pol)
                for d, a in zip(D, combo): q[idx[d]] = a
                v = cond(tuple(q), pred)
                if v is not None and v > base: ok = False
        if ok: res.append(pol)
    return res
print("  TN-V2 values:", {pol: str(Vtn(pol)) for pol in pols})
fams = {"singletons": [['F'], ['E']], "grand": [['F', 'E']], "only {d_E}": [['E']], "only {d_F}": [['F']], "non-partition": [['F'], ['E'], ['F', 'E']]}
for mode in ('occ', 'event'):
    print(f"  mode={mode}: " + "; ".join(f"{k}: {conflict_free(v, mode)}" for k, v in fams.items()))
print("  event conditionals: E[r|full] =", {pol: str(cond(pol, OBS['F'])) for pol in pols}, " E[r|empty] =", {pol: str(cond(pol, OBS['E'])) for pol in pols})
pay3 = {'SSS': 2, 'SSH': 3, 'SHS': 2, 'SHH': 3, 'HSS': 3, 'HSH': 3, 'HHS': 3, 'HHH': 4}
def cf3(family):
    res = []
    for prof in pay3:
        ok = True
        for D in family:
            for combo in product('SH', repeat=len(D)):
                q = list(prof)
                for d, a in zip(D, combo): q[d] = a
                if pay3[''.join(q)] > pay3[prof]: ok = False
        if ok: res.append(prof)
    return res
print("  three-point table (no chance, O = T, occurrence = V): singletons", cf3([[0], [1], [2]]), "; {{d1,d2},{d3}}", cf3([[0, 1], [2]]), "; grand", cf3([[0, 1, 2]]))

# ------------------------------------------------------------------------------------------------ H
hdr("H. sanity: Stag Hunt, FR-12 tree, two-point mugging B_1'")
As = ['S', 'H']; outs_s = [(a, b) for a in As for b in As]
Vs = dict(zip(outs_s, map(F, [2, 0, 0, 1])))
Gs = BG(As, As, Vs, Vs, {o: Vs[o] + F(k, 100) for k, o in enumerate(outs_s)})
print("  Stag Hunt Nash/uniform-THPE per outcome:", {s(o): v for o, v in Gs.thpe_table().items()}, "| safe batnas:", safe_batnas(As, As, Vs))
Af1, Af2 = ['out', 'in'], ['x', 'y']; outs_f = [(a, b) for a in Af1 for b in Af2]
Vf = dict(zip(outs_f, map(F, [0, 0, 0, -1])))
for pref in outs_f[:3]:
    order = [pref] + [o for o in outs_f[:3] if o != pref] + [('in', 'y')]
    Gf = BG(Af1, Af2, Vf, Vf, rank_W(order))
    print(f"  FR-12 tree, W-max optimum {pref}: uniform-THPE outcomes {Gf.thpe_outcomes()}")
print("  FR-12 safe batnas:", safe_batnas(Af1, Af2, Vf))
# B_1': real point d (acts on tails) and simulated point d' (acts inside Omega's simulation) as two players; x=1, y=2
Vb = {('pay', 'pay'): (y - x) / 2, ('pay', 'refuse'): -x / 2, ('refuse', 'pay'): y / 2, ('refuse', 'refuse'): F(0)}
Gb1 = BG(Ap, Ap, Vb, Vb, {o: Vb[o] + F(k, 1000) for k, o in enumerate(Vb)})
print("  B_1' (real, sim) common payoff:", {s(o): str(v) for o, v in Vb.items()}, "-> uniform-THPE outcomes:", Gb1.thpe_outcomes(), "| safe batnas:", safe_batnas(Ap, Ap, Vb))
print("\ndone.")
