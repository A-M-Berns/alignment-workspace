"""L2 repair: independent re-derivation (exact rationals) of the reviewer's decisive numbers.

A. Skyrms 1990 s6 Mean Demon (-50,0;0,-100): Jeffrey V vs Savage U at a state of indecision x = P(A1),
   under PERFECT prediction (P(S_i|A_i)=1; shared seed) and under a Definition-6 SAMPLER (P(S1|A_i)=x).
B. v2 Remark 4.3 miniature (0,2;1,0): same grid.
C. Skyrms's Nice Demon (1,0;0,2): fixed points under the Definition-6 sampler (C2/L3-11's {2/3, d1, d2}),
   and under the researcher's L2-15 THRESHOLD construction (state S1 iff d(A1) > 1/2).
D. Weatherson Table 6.1 (A:(3,5), B:(4,3) vs PA,PB): Nash vs strategic Demon (paid for a correct prediction)
   versus the fixed point against a Definition-6 sampler of Chooser's own mixture.
Fixed-point reading throughout: label x approved iff supp(x) is contained in the argmax of the (total) evaluator.
"""
from fractions import Fraction as F

def grid(n=60):
    return [F(k, n) for k in range(n + 1)]

def evaluators(u, x, semantics):
    # u[(i,j)]: payoff of act i when the predictor's output is j; i,j in {1,2}
    if semantics == 'PERFECT':
        cond = {(1, 1): F(1), (1, 2): F(0), (2, 1): F(0), (2, 2): F(1)}
    else:  # SAMPLER (Definition 6): predictor draws an independent sample from the mixture x
        cond = {(1, 1): x, (1, 2): 1 - x, (2, 1): x, (2, 2): 1 - x}
    V = {i: sum(cond[(i, j)] * u[(i, j)] for j in (1, 2)) for i in (1, 2)}          # Jeffrey
    U = {i: (x * u[(i, 1)] + (1 - x) * u[(i, 2)]) for i in (1, 2)}                  # Savage, P(S1) = x
    return V, U

def fixed_points(u, semantics, which):
    out = []
    for x in grid():
        V, U = evaluators(u, x, semantics)
        vals = V if which == 'Jeffrey' else U
        best = max(vals.values())
        supp = [i for i, p in ((1, x), (2, 1 - x)) if p > 0]
        if all(vals[i] == best for i in supp):
            out.append(x)
    return out

tables = {
    "A. Skyrms Mean Demon (-50,0;0,-100)": {(1, 1): F(-50), (1, 2): F(0), (2, 1): F(0), (2, 2): F(-100)},
    "B. v2 Remark 4.3 miniature (0,2;1,0)": {(1, 1): F(0), (1, 2): F(2), (2, 1): F(1), (2, 2): F(0)},
    "C. Skyrms Nice Demon (1,0;0,2)": {(1, 1): F(1), (1, 2): F(0), (2, 1): F(0), (2, 2): F(2)},
}
for name, u in tables.items():
    print("=" * 78); print(name)
    for sem in ('PERFECT', 'SAMPLER'):
        V, U = evaluators(u, F(2, 3), sem)
        print(f"  {sem}: at x=2/3  Jeffrey V={dict(V)}  Savage U={dict(U)}")
        for which in ('Jeffrey', 'Savage'):
            fp = fixed_points(u, sem, which)
            print(f"    fixed points ({which}, total evaluator, grid 1/60): {fp}")

# C'. the researcher's L2-15 threshold demon for the Nice Demon: state S1 iff d(A1) > 1/2 (predicts the MIXTURE by threshold)
print("=" * 78); print("C'. Nice Demon, THRESHOLD demon (S1 iff x > 1/2): both evaluators see the state as fixed given x")
u = tables["C. Skyrms Nice Demon (1,0;0,2)"]
fp = []
for x in grid():
    s1 = x > F(1, 2)
    vals = {i: (u[(i, 1)] if s1 else u[(i, 2)]) for i in (1, 2)}
    best = max(vals.values()); supp = [i for i, p in ((1, x), (2, 1 - x)) if p > 0]
    if all(vals[i] == best for i in supp): fp.append(x)
print("    fixed points:", fp, " (two pure labels, no interior tie: the threshold construction is neither Skyrms's perfect demon nor a Definition-6 sampler)")

# D. Weatherson Table 6.1
print("=" * 78); print("D. Weatherson Table 6.1  A:(3,5) B:(4,3) vs PA,PB")
pay = {("A", "PA"): F(3), ("A", "PB"): F(5), ("B", "PA"): F(4), ("B", "PB"): F(3)}
def chooser(p):  # p = P(Demon predicts A)
    return {a: p * pay[(a, "PA")] + (1 - p) * pay[(a, "PB")] for a in ("A", "B")}
# strategic Demon paid 1 for a correct prediction: indifferent iff Chooser plays A w.p. 1/2; Chooser indifferent iff p = 2/3
p_star = [p for p in grid() if chooser(p)["A"] == chooser(p)["B"]]
print("    Chooser indifferent iff P(PA) =", p_star, "; printed '1/3' gives", dict(chooser(F(1, 3))))
print("    strategic Demon indifferent iff Chooser P(A) = 1/2  ->  Nash (Chooser 1/2, Demon 2/3)")
# sampler: Demon's P(PA) = Chooser's own q; fixed point where Chooser is indifferent to her own statistics
fp = [q for q in grid() if all(chooser(q)[a] == max(chooser(q).values()) for a, pr in (("A", q), ("B", 1 - q)) if pr > 0)]
print("    Definition-6 sampler fixed points (Chooser's q):", fp, " -> 2/3, not 1/2: different game, different number")
