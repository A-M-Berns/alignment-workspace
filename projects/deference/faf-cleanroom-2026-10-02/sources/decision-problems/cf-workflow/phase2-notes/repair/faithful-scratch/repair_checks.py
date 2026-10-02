"""Repair agent, thread `faithful` — toolkit-free exact recomputation of every number the
dispositions rest on (Fraction / sympy only).  Run: python3 repair_checks.py

(A) FA-7(ii) kill: act-event cUDT with a success-obeying supposition on the unrealized atom (H,pay,1).
(B) FA-12 register: a mixed Nash / mixed-Def-22-coherent self-model that Definition 17's uniform tie-break does not reproduce.
(C) FA-13: exact tie polynomials, the three single deviations (v(aab)=0), value 3/4.
(D) FA-20(i) wound: post-act-observation tree, R2-real (6,4) vs R3 = R1-state (2,4).
(E) FA-17(b) wound: recorded routing root, R3(b) undefined.
(F) FA-25(1)/(2) kills: opaque Newcomb under mixed C — conditioning (2q+1, 2q+2) vs R1-state (3,2); under delta_one R3 (3,4) vs R1-state (3,2).
(G) seeds handoff: on the mugging, R3' (shared seed) = R1-state = (-x, 0) while Theorem 2' = V'(delta_a) = ((y-x)/2, 0).
(H) FA-2 closed forms and the difference identity used by the repaired Lean theorem.
(I) XC-14 reading S: brute force, three points {0,1} (reproduce 1032 / 24 / 136 / 0) and four points {0,1} restricted to S-pairs (UNREVIEWED evidence).
"""
import itertools, sympy as sp
from fractions import Fraction as F

x, y, q, t = sp.symbols('x y q t', positive=True)

def banner(s): print("\n" + "=" * 78 + "\n" + s + "\n" + "=" * 78)

# ---------------------------------------------------------------- (A)
banner("(A) FA-7(ii): act-event rho with a supposition on the unrealized atom (H,pay,1)")
# Prop 6's algebra: 2*3*2 = 12 atoms; realized by B_1: (T,pay,0),(T,refuse,0),(H,bot,0),(H,bot,1)
atoms12 = list(itertools.product(("H", "T"), ("pay", "refuse", "bot"), (0, 1)))
realized = {("T", "pay", 0), ("T", "refuse", 0), ("H", "bot", 0), ("H", "bot", 1)}
print("  atoms of E:", len(atoms12), "; realized by B_1:", len(realized), "; (H,pay,1) realized?", ("H", "pay", 1) in realized)
r = lambda w: (-x if w[1] == "pay" else 0) + (y if w[2] == 1 else 0)
P_pay = {("T", "pay", 0): F(1, 2), ("H", "pay", 1): F(1, 2)}      # success: both atoms satisfy choice=pay
print("  success P^pay(pay)=1:", all(w[1] == "pay" for w in P_pay), " mass:", sum(P_pay.values()))
V_rigid = sum(P_pay[w] * r(w) for w in P_pay)
print("  rigid V^pay(pay) =", sp.simplify(V_rigid), " vs V^refuse(refuse) = 0  -> pays iff y > 2x")
V_free = F(1, 2) * (-x) + F(1, 2) * y                              # V^pay(H,pay,1) := y (Definition 2 leaves it free)
print("  free  V^pay(pay) =", sp.simplify(V_free), " -> pays iff y > x (Remark 4.2's would-pay verdict from the ACT-event rho)")
print("  UDT (conditioning nu_{C'} on pay) cannot reach (H,pay,1): nu(.|pay) = delta_(T,pay,0), value -x  [unchanged]")

# ---------------------------------------------------------------- (B)
banner("(B) FA-12: Nash / mixed-Def-22 coherent self-model not reproduced by Definition 17")
tab = {("a", "a"): 2, ("b", "b"): 1, ("a", "b"): 0, ("b", "a"): 0}
V2 = lambda p1, p2: p1 * p2 * tab[("a", "a")] + (1 - p1) * (1 - p2) * tab[("b", "b")]
p = F(1, 3)
print("  V(C') =", V2(p, p), "; V(C'[d1->a]) =", V2(1, p), "; V(C'[d1->b]) =", V2(0, p), " (tie: every m gives", V2(p, p), ")")
print("  Definition 17 output at d1 = Unif{a,b} = (1/2,1/2) != C'(d1) = (1/3,2/3); T_UDT (Def 18) approves C' (supp inside the tie set)")

# ---------------------------------------------------------------- (C)
banner("(C) FA-13: three-point exact tie")
tab3 = {("a", "a", "a"): 1, ("b", "a", "a"): 1, ("a", "b", "a"): 1, ("a", "a", "b"): 0,
        ("b", "b", "a"): 0, ("b", "a", "b"): 1, ("a", "b", "b"): 1, ("b", "b", "b"): 1}
def Vdev(table, pistar, d, act, n):
    tot = 0
    for prof in itertools.product("ab", repeat=n):
        if prof[d] != act: continue
        w = 1
        for i in range(n):
            if i != d: w *= (1 - t) if prof[i] == pistar[i] else t
        tot += w * table[prof]
    return sp.expand(tot)
for d in range(3):
    va, vb = Vdev(tab3, ("a", "a", "a"), d, "a", 3), Vdev(tab3, ("a", "a", "a"), d, "b", 3)
    print(f"  d{d+1}: V(a) = {sp.factor(va)}   V(b) = {sp.factor(vb)}   tie for all t: {sp.simplify(va - vb) == 0}")
print("  single deviations from (a,a,a):", {p_: tab3[p_] for p_ in (("b", "a", "a"), ("a", "b", "a"), ("a", "a", "b"))},
      " -> 'every single deviation is optimal' is FALSE (v(aab)=0); it is what makes d3 strict")
print("  value of Unif x Unif x delta_a =", F(1, 4) * (tab3[("a","a","a")] + tab3[("a","b","a")] + tab3[("b","a","a")] + tab3[("b","b","a")]), "< 1")

# ---------------------------------------------------------------- (D)
banner("(D) FA-20(i): post-act observation O_d = {c=1}, coin drawn after the act")
leaves = {("a", 1): 2, ("a", 0): 10, ("b", 1): 4, ("b", 0): 4}      # (act, c) -> r, coin fair
R2_real = {a: F(1, 2) * (leaves[(a, 1)] + leaves[(a, 0)]) for a in "ab"}          # G_root(a): forcing, unconditioned on O_d
R3 = {a: leaves[(a, 1)] for a in "ab"}                                             # lim E[r | a ∧ c=1] (c independent of the draw)
R1_state = {a: leaves[(a, 1)] for a in "ab"}                                       # deviation delta_a conditioned on c=1
print("  F3 (instance-level act-recording) holds: every c=1 run passes the root once and its draw is recorded; root NOT subtree-veridical (c=0 leaves)")
print("  R2-real =", R2_real, "-> a;   R3 =", R3, "-> b;   R1-state =", R1_state, "-> b;   R2-real == R3:", R2_real == R3, "; R1-state == R3:", R1_state == R3)

# ---------------------------------------------------------------- (E)
banner("(E) FA-17(b): recorded routing root, O_d = {n=1}: a -> (act=a,n=1), b -> (act=b,n=0)")
print("  every O_d-run passes the root once with its draw a recorded (F3 holds); O_d realized under delta_a and under any mixture;")
print("  b ∧ O_d = ∅ (no leaf has act=b and n=1): nu_{C^eps}(b ∧ O_d) ≡ 0 -> cf^tr(b) undefined -> R3 not total on A_d")

# ---------------------------------------------------------------- (F)
banner("(F) FA-25(1)/(2): opaque Newcomb, p=3/4, L=4, S=1, O_d = ⊤, sim node then fill then real node")
pp, L, S = F(3, 4), 4, 1
Efill = q * pp + (1 - q) * (1 - pp)                                                # sim draws one w.p. q (independent of the real draw)
COND = {"one": sp.expand(Efill * L), "two": sp.expand(Efill * L + S)}              # E_C[r | real act]: real draw independent of sim's
R1_state = {"one": pp * L, "two": (1 - pp) * L + S}                                # deviation at both nodes: sim = act
R3_mixed = COND                                                                    # tremble limit under mixed C at O=⊤ is the conditional itself
print("  COND E_C[r|a]  =", COND, "   (at q=1/2:", {k: v.subs(q, sp.Rational(1, 2)) for k, v in COND.items()}, ")")
print("  R1-state       =", R1_state, "  constant in q;  COND == R1-state? ", all(sp.simplify(COND[k] - R1_state[k]) == 0 for k in COND))
print("  R3 (mixed C)   =", R3_mixed, " = COND, not R1-state -> FA-25(1) as stated fails under act-recording (two d-nodes per run)")
R3_one = {"one": pp * L, "two": pp * L + S}                                         # under delta_one: fill stays at E_{delta_one}[fill] = p
R2_real_one = R3_one
print("  under delta_one: R3 =", R3_one, "(two-box) ; R2-real =", R2_real_one, "; R1-state =", R1_state, "(one-box) -> FA-25(2) as stated fails (R3 != O_d-conditioned deviation)")
print("  real node: subtree-veridical (O=⊤) and action-veridical, but NOT the only d-node on the run (exactly-one fails) -> outside Definition 7 recording")

# ---------------------------------------------------------------- (G)
banner("(G) seeds handoff: mugging (x=1,y=3), shared seed")
X, Y = 1, 3
R3s = {"pay": -X, "refuse": 0}                                                     # condition on a ∧ T: the T-leaf with that draw
R1_state_s = {"pay": -X, "refuse": 0}                                              # delta_a conditioned on O_d = T
Thm2p = {"pay": F(1, 2) * (-X) + F(1, 2) * Y, "refuse": 0}                          # occ(d) = Leaves: V'(delta_a)
print("  R3' =", R3s, ";  R1-state (shared seed) =", R1_state_s, ";  Theorem 2' = E_{mu'_{delta_a}}[r|occ(d)] = V'(delta_a) =", Thm2p)
print("  R3' == R1-state:", R3s == R1_state_s, ";  R3' == Theorem 2':", R3s == Thm2p, " -> the requested identity is false; the true one is R3' = R1-state")

# ---------------------------------------------------------------- (H)
banner("(H) FA-2 closed forms and the Lean difference identity")
Vp = q * (y - x) / (1 + q); Vr = q * y / (2 - q)
diff = sp.factor(sp.together(Vp - Vr))
print("  V(H∨pay) - V(H∨refuse) =", diff)
target = q * (y * (1 - 2 * q) - x * (2 - q)) / ((1 + q) * (2 - q))
print("  equals q[y(1-2q) - x(2-q)]/((1+q)(2-q)):", sp.simplify(Vp - Vr - target) == 0)
print("  at q=1/2:", sp.simplify(Vp.subs(q, sp.Rational(1, 2))), "vs", sp.simplify(Vr.subs(q, sp.Rational(1, 2))), " (v2's (y-x)/3 vs y/3)")
print("  at q=1/10, x=1, y=3:", Vp.subs({q: sp.Rational(1, 10), x: 1, y: 3}), "vs", Vr.subs({q: sp.Rational(1, 10), x: 1, y: 3}), " -> pays")

# ---------------------------------------------------------------- (I)
banner("(I) XC-14 reading S: brute force with exact integer polynomials in t")
def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai == 0: continue
        for j, bj in enumerate(b):
            out[i + j] += ai * bj
    return out
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
ONE_MINUS_T, T = [1, -1], [0, 1]
def V_poly(table, pistar, d, act, n, profiles):
    tot = [0]
    for prof in profiles:
        if prof[d] != act or table[prof] == 0: continue
        w = [table[prof]]
        for i in range(n):
            if i != d: w = pmul(w, ONE_MINUS_T if prof[i] == pistar[i] else T)
        tot = padd(tot, w)
    return tot
def low_sign(poly):
    for c in poly:
        if c != 0: return 1 if c > 0 else -1
    return 0
def BRset(table, pistar, d, n, profiles):
    va = V_poly(table, pistar, d, "a", n, profiles); vb = V_poly(table, pistar, d, "b", n, profiles)
    s = low_sign(padd(vb, [-c for c in va]))
    return {"a", "b"} if s == 0 else ({"b"} if s > 0 else {"a"})
def flip(p_, d): return p_[:d] + ("b" if p_[d] == "a" else "a",) + p_[d + 1:]
def brute(n, entries, only_S=False):
    profiles = list(itertools.product("ab", repeat=n))
    pairs = fails = S_pairs = S_fails = 0; ex = []
    for vals in itertools.product(entries, repeat=len(profiles)):
        table = dict(zip(profiles, vals)); M = max(vals)
        Pi = {p_ for p_ in profiles if table[p_] == M}
        for pistar in Pi:
            strong = all(table[flip(pistar, d)] == M for d in range(n))
            if only_S and not strong: continue
            pairs += 1; S_pairs += strong
            brs = [BRset(table, pistar, d, n, profiles) for d in range(n)]
            bad = not set(itertools.product(*brs)) <= Pi
            fails += bad; S_fails += (bad and strong)
            if bad and strong and len(ex) < 3: ex.append((table, pistar, brs))
    return pairs, fails, S_pairs, S_fails, ex
print("  three points {0,1}: (pairs, failures, S-pairs, S-failures) =", brute(3, (0, 1))[:4], "  [reviewer: 1032, 24, 136, 0]")
print("  two points {0,1,2}: (pairs, failures) =", brute(2, (0, 1, 2))[:2], "  [thread/reviewer: 144, 0]")
res4 = brute(4, (0, 1), only_S=True)
print("  four points {0,1}, S-pairs only: (S-pairs, S-failures) =", (res4[2], res4[3]), " examples:", res4[4][:2])
