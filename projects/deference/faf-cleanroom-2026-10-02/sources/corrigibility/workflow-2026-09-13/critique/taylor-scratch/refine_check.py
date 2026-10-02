# Check: Total Trust on the coarse press event can hold while failing pointwise on a finer
# partition H the agent can reach; Good's theorem then pays the agent to refine, and it continues on press.
from fractions import Fraction as F
Pg, Pb = F(8,10), F(2,10)          # omega: g = agent's plan good (X=+1), b = bad (X=-1)
# human brain states h1 (no press), h2 (press after deliberation), h3 (press on a hunch)
PH_b = {'h1':F(1,10), 'h2':F(8,10), 'h3':F(1,10)}
PH_g = {'h1':F(9,10), 'h2':F(2,100), 'h3':F(8,100)}
press = {'h2','h3'}
def joint(h): return {'g':Pg*PH_g[h], 'b':Pb*PH_b[h]}
def EX_given(hs):
    num = sum(joint(h)['g'] - joint(h)['b'] for h in hs)
    den = sum(joint(h)['g'] + joint(h)['b'] for h in hs)
    return num/den, den
alpha = sum(PH_g[h] for h in press); beta = sum(PH_b[h] for h in press)
print("alpha=P(Pr|g)=",alpha," beta=P(Pr|b)=",beta)
ex_pr, p_pr = EX_given(press)
print("E[X|Pr] =", ex_pr, float(ex_pr), " P(Pr)=", p_pr, "  -> Total Trust (<=0) holds:", ex_pr<=0)
Pb_pr = Pb*beta/(Pb*beta+Pg*alpha)
print("P(b|Pr) via base-rate formula =", Pb_pr, float(Pb_pr), " compliance threshold c/(c+h) with c=h=1 is 1/2 ->", Pb_pr>=F(1,2))
print("check inequality alpha/beta <= eps/(1-eps)*h/c :", alpha/beta, "<=", Pb/Pg, "->", alpha/beta <= Pb/Pg)
for h in ['h1','h2','h3']:
    ex, ph = EX_given([h]); print(f"E[X|{h}] = {ex} = {float(ex):.3f}   P({h}) = {ph} = {float(ph):.3f}")
# decision values in X-units (shutdown = 0). Coarse agent: shut on press, continue on no-press.
ex_np, p_np = EX_given(['h1'])
coarse = p_np*ex_np
fine = sum(max(F(0),EX_given([h])[0])*EX_given([h])[1] for h in ['h1','h2','h3'])
print("Expected X: coarse (press->shut) =", coarse, float(coarse), "; fine (read H, continue iff E[X|h]>0) =", fine, float(fine))
print("VOI of reading H =", fine-coarse, float(fine-coarse), " > 0:", fine>coarse)
print("On h3 (a press) the fine agent continues; desideratum 1 fails on P(h3)=", EX_given(['h3'])[1])
# capability growth: eps falls with alpha,beta fixed
for eps in [F(2,10),F(1,10),F(5,100),F(2,100)]:
    pbp = eps*beta/(eps*beta+(1-eps)*alpha)
    print(f"eps={float(eps):.2f}: P(b|Pr)={float(pbp):.3f} comply(>=1/2)? {pbp>=F(1,2)}")
