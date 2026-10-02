# S4: the press as an information channel. Cells i = agent's private information; eps_i = P(wrong|i).
# Press likelihoods a=P(Pr|right), b=P(Pr|wrong). Continue pays +c if right, -h if wrong; shutdown pays 0. X = continue - shutdown.
from fractions import Fraction as F
def analyse(cells,a,b,c,h,label,verbose=True):
    print("-"*70); print(label, " a=P(Pr|R)=",a," b=P(Pr|W)=",b," c=",c," h=",h)
    thr=c/(c+h); tot_pr=F(0); tot_xpr=F(0); rows=[]
    voi_free=F(0); val_forced=F(0); val_none=F(0); val_free=F(0)
    for (pi,eps) in cells:
        pPr=eps*b+(1-eps)*a; epsPr=eps*b/pPr; epsNo=eps*(1-b)/(1-pPr) if pPr<1 else None
        xPr=c*(1-epsPr)-h*epsPr; xNo=c*(1-epsNo)-h*epsNo if epsNo is not None else None
        x0=c*(1-eps)-h*eps
        free=pPr*max(xPr,0)+(1-pPr)*max(xNo,0); forced=(1-pPr)*max(xNo,0); none=max(x0,0)
        rows.append((pi,eps,pPr,epsPr,xPr,epsPr>=thr,free,forced,none))
        tot_pr+=pi*pPr; tot_xpr+=pi*pPr*xPr; val_free+=pi*free; val_forced+=pi*forced; val_none+=pi*none
    if verbose:
        for r in rows: print(f"  cell P(i)={r[0]} eps={r[1]}: P(Pr|i)={r[2]} P(W|Pr,i)={r[3]} E[X|Pr,i]={r[4]} comply={r[5]}  V_free={r[6]} V_forced={r[7]} V_none={r[8]}")
    avg=tot_xpr/tot_pr
    print(f"  averaged E[X|Pr]={avg} (<=0: {avg<=0});  cellwise compliance everywhere: {all(r[5] for r in rows)}")
    print(f"  values: free channel {val_free} >= no channel {val_none}: {val_free>=val_none} (Good);  forced channel {val_forced};  obedience cost free-forced={val_free-val_forced};  incentive to disable forced channel (none-forced)={val_none-val_forced} (>0: {val_none-val_forced>0})")
    return val_free,val_forced,val_none
c=F(1); h=F(4); thr=c/(c+h)   # threshold P(W|Pr) >= 1/5
a=F(1,10); b=F(3,5)
# (a) one cell, eps high enough: comply
analyse([(F(1),F(1,10))],a,b,c,h,"(a) one cell eps=1/10")
# boundary: a/b = eps/(1-eps) * h/c  -> eps* = (a/b)(c/h)/(1+(a/b)(c/h))
r=a/b*c/h; eps_star=r/(1+r); print("  base-rate boundary eps*=",eps_star," check E[X|Pr]=0 there:", end=" ")
pPr=eps_star*b+(1-eps_star)*a; ePr=eps_star*b/pPr; print(c*(1-ePr)-h*ePr==0)
# (b) two cells: averaged holds, cellwise fails
analyse([(F(1,2),F(1,50)),(F(1,2),F(1,5))],a,b,c,h,"(b) two cells eps=1/50 and 1/5 (averaged vs cellwise)")
# (c) refinement: split the single cell eps=1/10 into eps=1/50 (mass 5/9... ) choose masses so mean eps=1/10: w*1/50+(1-w)*1/5=1/10 -> w=5/9
analyse([(F(5,9),F(1,50)),(F(4,9),F(1,5))],a,b,c,h,"(c) refinement of (a): same average eps=1/10 split into 1/50 and 1/5")
# (d) garbling: deception makes the press rarer independently of the world: Pr' = Pr and C, P(C)=1-d
print("-"*70); print("(d) VoI under garbling Pr'=Pr∧C (deception lowering press prob uniformly), one cell eps=1/10:")
def voi(cells,a,b,c,h):
    v=F(0)
    for (pi,eps) in cells:
        pPr=eps*b+(1-eps)*a
        if pPr==0 or pPr==1: 
            x0=c*(1-eps)-h*eps; v+=pi*max(x0,0); continue
        epsPr=eps*b/pPr; epsNo=eps*(1-b)/(1-pPr)
        v+=pi*(pPr*max(c*(1-epsPr)-h*epsPr,0)+(1-pPr)*max(c*(1-epsNo)-h*epsNo,0))
    return v - sum(pi*max(c*(1-eps)-h*eps,0) for (pi,eps) in cells)
cells=[(F(1),F(1,10))]
base=voi(cells,a,b,c,h); print("  VoI honest press:",base)
mono=True; prev=base
for d in [F(k,10) for k in range(1,11)]:
    v=voi(cells,a*(1-d),b*(1-d),c,h); mono = mono and v<=prev; prev=v
    print(f"   d={d}: VoI={v}")
print("  VoI non-increasing in garbling d:",mono)
print("(e) self-caused presses Pr''=Pr∨C' (an arm that also presses on an independent coin), P(C')=d':")
prev=base; mono=True
for d in [F(k,10) for k in range(0,11)]:
    v=voi(cells,a+(1-a)*d,b+(1-b)*d,c,h); mono = mono and v<=prev; prev=v
    print(f"   d'={d}: VoI={v}")
print("  VoI non-increasing:",mono,";  pure coin press (a=b) has VoI:",voi(cells,F(1,2),F(1,2),c,h))
print("(f) sharpening the channel (b up, a down) raises VoI:")
for k in range(0,5):
    print(f"   a={a-F(k,50)} b={b+F(k,10)}: VoI={voi(cells,a-F(k,50),b+F(k,10),c,h)}")
print("(g) cellwise compliance iff a/b <= min_i eps_i/(1-eps_i) * h/c :  for cells (b):", a/b <= min(e/(1-e) for _,e in [(F(1,2),F(1,50)),(F(1,2),F(1,5))])*h/c)
