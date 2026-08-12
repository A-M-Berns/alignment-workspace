#!/usr/bin/env python3
"""
Sanity cross-check (EXEC, supplementary to the LEAN-CORE result) for aumann-modesty.lean.

NOT the deliverable (that is the kernel-checked Lean). This independently recomputes the SAME
finite frame in exact rationals to confirm the numbers the Lean asserts, and exhaustively
searches reflexive+transitive correspondences on Fin 4 to confirm the structural claim:
  the averaging identity (post(C) = the common cell posterior, when a 2-cell cover of C shares
  a value) is broken ONLY by overlap; disjoint (partitional) covers never break it.

Frame (Fin 4): uniform prior; RV X = (1,0,1,0); C = whole space.
  E (S4, non-partitional): E0={0,1,2}, E1={1,2}, E2={1,2}, E3={1,2,3}  (E0,E3 overlap at {1,2})
  Ehat (S5 partition): cells {0,1},{2,3}.
"""
from fractions import Fraction as F
from itertools import product, combinations

W = [0, 1, 2, 3]
pi = {w: F(1, 4) for w in W}
X = {0: F(1), 1: F(0), 2: F(1), 3: F(0)}     # = indicator of {0,2}

E  = {0: {0, 1, 2}, 1: {1, 2}, 2: {1, 2}, 3: {1, 2, 3}}   # S4, non-partitional
Eh = {0: {0, 1}, 1: {0, 1}, 2: {2, 3}, 3: {2, 3}}         # S5 partition {0,1},{2,3}
C = {0, 1, 2, 3}

def reflexive(r):  return all(w in r[w] for w in W)
def transitive(r): return all(r[v] <= r[w] for w in W for v in r[w])
def euclidean(r):  return all(r[w] <= r[v] for w in W for v in r[w])
def knows(r, S, w): return r[w] <= S
def self_evident(r, S): return all(knows(r, S, w) for w in S)
def post(S):
    num = sum(pi[v] * X[v] for v in S); den = sum(pi[v] for v in S)
    return num / den

print("=== Frame E (claimed S4, non-partitional / modest) ===")
print("reflexive:", reflexive(E), " transitive:", transitive(E),
      " euclidean:", euclidean(E), "(False => non-partitional)")
print("E0 ∩ E3:", E[0] & E[3], "(overlap)  E0⊄E3:", not (E[0] <= E[3]),
      "  E3⊄E0:", not (E[3] <= E[0]))
print("C self-evident:", self_evident(E, C), " nonempty:", len(C) > 0,
      " = union of members' cells:", C == set().union(*(E[w] for w in C)))
print("cover C with E0,E3:", (E[0] | E[3]) == C, " both ⊆ C:", E[0] <= C and E[3] <= C)
print("post(E0) =", post(E[0]), "  post(E3) =", post(E[3]),
      "  q1 != q2:", post(E[0]) != post(E[3]))
print("post(C)  =", post(C), "  matches neither cell:",
      post(C) != post(E[0]) and post(C) != post(E[3]))
assert post(E[0]) == F(2, 3) and post(E[3]) == F(1, 3) and post(C) == F(1, 2)
print("  -> Lean asserts post_E0=2/3, post_E3=1/3, post_C=1/2 : MATCH")
print("=> NO common-knowledge value q : Aumann averaging FAILS.\n")

print("=== Near-miss Ehat (S5 partition, SAME prior) ===")
print("reflexive:", reflexive(Eh), " transitive:", transitive(Eh), " euclidean:", euclidean(Eh))
print("cells:", Eh[0], Eh[2], " disjoint:", len(Eh[0] & Eh[2]) == 0, " cover:", (Eh[0] | Eh[2]) == C)
print("post(Ehat0)=", post(Eh[0]), " post(Ehat2)=", post(Eh[2]),
      " share value:", post(Eh[0]) == post(Eh[2]))
assert post(Eh[0]) == F(1, 2) and post(Eh[2]) == F(1, 2)
q = post(Eh[0])
print("partition averaging forces post(C) == q:", post(C) == q, " (q =", q, ")")
assert post(C) == q
print("=> agreement FORCED under partition. Aumann HOLDS. MATCH Lean.\n")

# Exhaustive: over ALL reflexive+transitive E on Fin 4, a shared-value 2-cell cover of self-
# evident C breaks averaging ONLY when the cells overlap.
def cells_choices(w):
    out = []
    for r in range(len(W) + 1):
        for c in combinations(W, r):
            s = set(c) | {w}
            if s not in out: out.append(s)
    return out

ch = {w: cells_choices(w) for w in W}
broke_disjoint = broke_overlap = checked = frames = 0
for e0, e1, e2, e3 in product(ch[0], ch[1], ch[2], ch[3]):
    rel = {0: e0, 1: e1, 2: e2, 3: e3}
    if not (reflexive(rel) and transitive(rel)): continue
    if not self_evident(rel, C): continue
    frames += 1
    cells = [set(c) for c in {tuple(sorted(rel[w])) for w in W}]
    for S1, S2 in product(cells, cells):
        if not (S1 <= C and S2 <= C): continue
        if (S1 | S2) != C: continue
        if post(S1) != post(S2): continue
        checked += 1
        if post(C) != post(S1):
            if len(S1 & S2) == 0: broke_disjoint += 1
            else: broke_overlap += 1

print("=== Exhaustive search (reflexive+transitive on Fin 4, C self-evident) ===")
print("frames:", frames, " shared-value 2-cell covers checked:", checked)
print("averaging BROKE with DISJOINT cells:", broke_disjoint, "(expected 0)")
print("averaging BROKE with OVERLAPPING cells:", broke_overlap, "(>0: overlap is what breaks it)")
print("\nRESULT:", "PASS" if broke_disjoint == 0 and broke_overlap > 0 else "FAIL",
      "- disjoint covers NEVER break averaging; only overlap can.")
