# S1: structure of the class of legitimizing events in a finite two-time model.
# Exact rationals. Atoms: (name, phi in {0,1}, announced future credence c, weight).
from fractions import Fraction as F
from itertools import combinations

def run(atoms, label):
    print("="*70); print(label)
    names=[a[0] for a in atoms]; n=len(atoms)
    tot=sum(a[3] for a in atoms); assert tot==1, tot
    cells=sorted(set(a[2] for a in atoms))
    def mass(S): return sum(atoms[i][3] for i in S)
    def legit(S):
        # S is a frozenset of atom indices. Legitimizing iff for each cell c with P(S∩C_c)>0: P(phi∩S∩C_c)=c*P(S∩C_c)
        for c in cells:
            cell=[i for i in S if atoms[i][2]==c]
            if not cell: continue
            m=mass(cell); h=sum(atoms[i][3] for i in cell if atoms[i][1]==1)
            if h!=c*m: return False
        return True
    allsets=[frozenset(S) for k in range(n+1) for S in combinations(range(n),k)]
    L=[S for S in allsets if legit(S)]
    Omega=frozenset(range(n))
    print("atoms:",[(a[0],a[1],str(a[2]),str(a[3])) for a in atoms])
    for c in cells:
        cell=[i for i in range(n) if atoms[i][2]==c]; m=mass(cell); h=sum(atoms[i][3] for i in cell if atoms[i][1]==1)
        print(f" cell c={c}: hits={h} misses={m-h} freq={h/m} calibrated={h/m==c}  atomless-max-legit-mass=min(h/c,m'/(1-c))={min(h/c,(m-h)/(1-c))}")
    print("unconditional reflection (Omega legitimizing):", Omega in L)
    print("number of legitimizing events (incl. empty):",len(L))
    nonempty=[S for S in L if S]
    print("legitimizing events:",[sorted(names[i] for i in S) for S in nonempty])
    # closure checks
    Lset=set(L)
    dis_ok=all((A|B) in Lset for A in L for B in L if not (A&B))
    diff_ok=all((A-B) in Lset for A in L for B in L if B<=A)
    print("closed under disjoint unions:",dis_ok,"| closed under proper differences:",diff_ok)
    union_fail=[(sorted(names[i] for i in A),sorted(names[i] for i in B)) for A in L for B in L if (A&B) and (A|B) not in Lset]
    inter_fail=[(sorted(names[i] for i in A),sorted(names[i] for i in B)) for A in L for B in L if (A&B) and (A&B) not in Lset]
    print("union failures (first 3):",union_fail[:3]," count:",len(union_fail))
    print("intersection failures (first 3):",inter_fail[:3]," count:",len(inter_fail))
    if Omega in L:
        comp_ok=all((Omega-A) in Lset for A in L)
        print("Omega legitimizing => complement-closed (Dynkin system):",comp_ok)
        inter_closed=all((A&B) in Lset for A in L for B in L)
        print("   ... but intersection-closed (sigma-algebra)?",inter_closed)
    # maximal-mass legitimizing events
    mx=max(mass(S) for S in L)
    maxi=[sorted(names[i] for i in S) for S in L if mass(S)==mx]
    print("maximal legitimate mass:",mx," achieved by:",maxi," (non-unique:",len(maxi)>1,")")
    bound=sum(min(sum(a[3] for a in atoms if a[2]==c and a[1]==1)/c, sum(a[3] for a in atoms if a[2]==c and a[1]==0)/(1-c)) for c in cells)
    print("atomless upper bound sum_c min(h_c/c, m_c/(1-c)) =",bound," attained:",bound==mx)
    # defect decomposition: for L legitimizing, per cell: P(phi|C)-c = P(L^c|C)*(P(phi|L^c,C)-c)
    ok=True
    for S in L:
        Sc=Omega-S
        for c in cells:
            C=[i for i in range(n) if atoms[i][2]==c]; mC=mass(C); hC=sum(atoms[i][3] for i in C if atoms[i][1]==1)
            Cc=[i for i in Sc if atoms[i][2]==c]
            if not Cc: 
                ok = ok and (hC/mC==c); continue
            mCc=mass(Cc); hCc=sum(atoms[i][3] for i in Cc if atoms[i][1]==1)
            lhs=hC/mC-c; rhs=(mCc/mC)*(hCc/mCc-c)
            ok = ok and (lhs==rhs)
    print("defect decomposition identity holds for every legitimizing L and cell:",ok)

# Model A: both cells miscalibrated (Omega not legitimizing)
A=[('a1',1,F(1,2),F(2,16)),('a2',1,F(1,2),F(1,16)),('a3',0,F(1,2),F(2,16)),('a4',0,F(1,2),F(2,16)),
   ('b1',1,F(3,4),F(3,16)),('b2',1,F(3,4),F(3,16)),('b3',0,F(3,4),F(1,16)),('b4',0,F(3,4),F(2,16))]
run(A,"MODEL A: both cells miscalibrated; unconditional reflection fails")
# Model B: both cells calibrated (Omega legitimizing)
B=[('a1',1,F(1,2),F(2,16)),('a2',1,F(1,2),F(2,16)),('a3',0,F(1,2),F(2,16)),('a4',0,F(1,2),F(2,16)),
   ('b1',1,F(3,4),F(3,16)),('b2',1,F(3,4),F(3,16)),('b3',0,F(3,4),F(1,16)),('b4',0,F(3,4),F(1,16))]
run(B,"MODEL B: both cells calibrated; unconditional reflection holds")
# Model C: fine atoms approximate the atomless bound
k=6
C=[]
for j in range(k): C.append((f'h{j}',1,F(1,2),F(3,16)/k))
for j in range(k): C.append((f'm{j}',0,F(1,2),F(4,16)/k))
C.append(('b1',1,F(3,4),F(6,16))); C.append(('b3',0,F(3,4),F(3,16)))
run(C,"MODEL C: cell A split into 12 fine atoms (3/16 hits, 4/16 misses at c=1/2); cell B coarse")
