"""L5 check 2: Arntzenius's Yankees v Red Sox (as restated by Ahmed & Price 2012 §2, READ
ahmed-price-2012-...txt:73-110) encoded as a v2 tree, versus Newcomb's problem.

Tree (Definition 5, independent redraws Def 6): chance g in {Y: 9/10, R: 1/10}; the perfect
announcer is realized by two hypothetical queries (r_w ~ C(d_win), r_l ~ C(d_lose)) and a
truth-seeking rule: announce 'win' if r_w wins at g, else 'lose' if r_l loses at g, else
(no truthful option) announce 'win' anyway (the contrarian convention; cf. Told-You-So's (10,5)
leaf). Then the real query at the announced point, fresh draw a ~ C(d_ann). Payoffs (Table 1):
BR: R->+2, Y->-1; BY: R->-2, Y->+1. Leaf world (g, ann, a, truthful).

Exact arithmetic; sympy for the symbolic self-model x and the tremble eps.
"""
from fractions import Fraction as F
import sympy as sp
from itertools import product

PG = {'Y': F(9,10), 'R': F(1,10)}
PAY = {('BR','R'): 2, ('BR','Y'): -1, ('BY','R'): -2, ('BY','Y'): 1}
def wins(bet, g): return (bet=='BR' and g=='R') or (bet=='BY' and g=='Y')

def run(C):
    """C = {'win': {'BR': p, 'BY': q}, 'lose': {...}} (weights may be sympy). Returns dict world->weight."""
    mu = {}
    for g, pg in PG.items():
        for r_w, pw in C['win'].items():
            for r_l, pl in C['lose'].items():
                if wins(r_w, g): ann, none = 'win', False
                elif not wins(r_l, g): ann, none = 'lose', False
                else: ann, none = 'win', True
                for a, pa in C[ann].items():
                    truthful = (ann == 'win') == wins(a, g)
                    w = (g, ann, a, truthful, none)
                    mu[w] = mu.get(w, 0) + pg*pw*pl*pa
    return mu

def det(bw, bl): return {'win': {bw: 1, 'BR' if bw=='BY' else 'BY': 0}, 'lose': {bl: 1, 'BR' if bl=='BY' else 'BY': 0}}
def value(mu): return sum(w*PAY[(k[2], k[0])] for k, w in mu.items())
def P(mu, pred): return sum(w for k, w in mu.items() if pred(k))
def cond(mu, pred, given):
    den = P(mu, given); return None if den == 0 else P(mu, lambda k: pred(k) and given(k))/den

print("=== (1) the four deterministic profiles (bet at 'win', bet at 'lose') ===")
for bw, bl in product(['BR','BY'], repeat=2):
    mu = run(det(bw, bl))
    tr = P(mu, lambda k: k[3]); none = P(mu, lambda k: k[4])
    print(f"profile ({bw},{bl}): V_B = {value(mu)} ; nu(truthful) = {tr} ; nu(no truthful announcement) = {none}")
    for ann in ('win','lose'):
        pY = cond(mu, lambda k: k[0]=='Y', lambda k, ann=ann: k[1]==ann)
        pBY = cond(mu, lambda k: k[2]=='BY', lambda k, ann=ann: k[1]==ann)
        print(f"     at O={ann}: nu(g=Y|O) = {pY} ; nu(a=BY|O) = {pBY}  (strict OC + recording forces P_s(a)=C(d)(a): Remark 3.6)")

print("\n=== (2) masked calibration at d_win (local self-model m = (BR:1-x, BY:x)) for the two constant profiles ===")
x = sp.symbols('x', positive=True)
for prof in (('BR','BR'), ('BY','BY')):
    C = det(*prof); C['win'] = {'BR': 1-x, 'BY': x}
    mu = run(C)
    W = lambda k: k[1]=='win'
    pT = sp.simplify(cond(mu, lambda k: k[3], W)); pY = sp.simplify(cond(mu, lambda k: k[0]=='Y', W))
    vBY = sp.simplify(sum(w*PAY[(k[2],k[0])] for k,w in mu.items() if W(k) and k[2]=='BY')/P(mu, lambda k: W(k) and k[2]=='BY'))
    vBR = sp.simplify(sum(w*PAY[(k[2],k[0])] for k,w in mu.items() if W(k) and k[2]=='BR')/P(mu, lambda k: W(k) and k[2]=='BR'))
    print(f"profile {prof}: at the m-state for O=win: P(truthful|win) = {pT} ; P(g=Y|win) = {pY}")
    print(f"     EDT act values: V(BY|win) = {vBY} ; V(BR|win) = {vBR} ; BY > BR iff {sp.solve(sp.Eq(vBY, vBR), x)} < x")
    for xv in (F(1,10), F(1,2), F(9,10)):
        print(f"       x={xv}: P(truthful|win)={pT.subs(x,xv)}, P(Y|win)={pY.subs(x,xv)}, V(BY)={vBY.subs(x,xv)}, V(BR)={vBR.subs(x,xv)}")

print("\n=== (3) limit calibration (Def 10): trembles eps at both points, the two constant profiles ===")
e = sp.symbols('epsilon', positive=True)
for prof in (('BR','BR'), ('BY','BY')):
    C = {pt: {b: (1-e)*(1 if b==prof[i] else 0) + e/2 for b in ('BR','BY')} for i, pt in enumerate(('win','lose'))}
    mu = run(C)
    print(f"profile {prof}: V_B(C^eps) = {sp.simplify(value(mu))} -> limit {sp.limit(value(mu), e, 0)}")
    for ann in ('win','lose'):
        A = lambda k, ann=ann: k[1]==ann
        pY = sp.simplify(cond(mu, lambda k: k[0]=='Y', A))
        vals = {}
        for b in ('BR','BY'):
            num = sum(w*PAY[(k[2],k[0])] for k,w in mu.items() if A(k) and k[2]==b); den = P(mu, lambda k, b=b: A(k) and k[2]==b)
            vals[b] = sp.limit(sp.simplify(num/den), e, 0)
        print(f"     O={ann}: lim P(g=Y|O) = {sp.limit(pY, e, 0)} ; limit act values V(BR)={vals['BR']}, V(BY)={vals['BY']} ; approves {max(vals, key=vals.get)} ; profile plays {prof[0] if ann=='win' else prof[1]}")

print("\n=== (4) contrast: Newcomb under local masking has ONE state for both procedures ===")
p, L, S = F(9,10), 10, 1
def newcomb(C1):  # C1 = prob of one-boxing; hypothetical draw h, fill ~ Bern(p) if h=one else Bern(1-p); real draw a
    mu = {}
    for h, ph in (('one', C1), ('two', 1-C1)):
        for fill, pf in ((1, p if h=='one' else 1-p), (0, (1-p) if h=='one' else p)):
            for a, pa in (('one', C1), ('two', 1-C1)):
                w = (fill, a); mu[w] = mu.get(w, 0) + ph*pf*pa
    return mu
for C1 in (F(1), F(0)):
    mu = newcomb(C1); print(f"  C(d)(one)={C1}: V_B = {sum(w*(k[0]*L + S*(k[1]=='two')) for k,w in mu.items())} ; strict state: P(fill)={P(mu, lambda k: k[0]==1)}, P(a=one)={P(mu, lambda k: k[1]=='one')}")
m = F(1,2); mu = newcomb(m)
print(f"  masked state with m=1/2 (the same for one-boxer and two-boxer since d is the only point): P(fill)={P(mu, lambda k: k[0]==1)}, P(fill|one)={cond(mu, lambda k: k[0]==1, lambda k: k[1]=='one')}, P(fill|two)={cond(mu, lambda k: k[0]==1, lambda k: k[1]=='two')}")
print("  => Definition 21's comparison class is non-empty for Newcomb at the masked grade (V: pL vs (1-p)L+S), and empty for Yankees at every grade:")
for prof in (('BR','BR'), ('BY','BY')):
    C = det(*prof); C['win'] = {'BR': F(1,2), 'BY': F(1,2)}; mu = run(C)
    print(f"     Yankees, profile {prof}, m=1/2 at d_win: P(g=Y | win) = {cond(mu, lambda k: k[0]=='Y', lambda k: k[1]=='win')}  (differs across profiles: the d_win state depends on C(d_lose) through the announcer)")
