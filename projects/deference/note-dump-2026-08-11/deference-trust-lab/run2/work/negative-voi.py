#!/usr/bin/env python3
"""
negative-voi.py  —  cross-check for run2/lean/negative-voi.lean (TODO `negative-voi`).

Independent ℚ verification of Weatherson's 3-world VoI-tightness witness, plus an EXHAUSTIVE
search certifying the example is NOT an artifact: over all S4 experiments on 3 worlds, with the
SAME genuine argmax-of-posterior recommended strategy, the strict negative-VoI inequality holds
ONLY when the coarser expert is non-partitional, and a refinement of any partitional experiment
never loses value (the Geanakoplos near-miss).

Run:  python3 negative-voi.py
"""
from itertools import product
from fractions import Fraction as F

W = [0, 1, 2]
pi = {0: F(1, 3), 1: F(1, 3), 2: F(1, 3)}

# === The exact witness formalized in Lean ===
# Menu O (two [0,1]-options):  O^0 = (0, 2/3, 1/3),  O^1 = (2/3, 0, 0)
O = [{0: F(0), 1: F(2, 3), 2: F(1, 3)},
     {0: F(2, 3), 1: F(0), 2: F(0)}]
# Experiments as cell-membership sets E[w] subseteq W
E1  = {0: {0}, 1: {1}, 2: {0, 2}}        # finer,  S4, NON-partitional
E2  = {0: {0}, 1: {1}, 2: {0, 1, 2}}     # coarser, S4, NON-partitional
Q   = {0: {0, 2}, 1: {1}, 2: {0, 2}}     # partition anchor (partitional)


# === Structural predicates ===
def reflexive(E):  return all(w in E[w] for w in W)
def transitive(E): return all(set(E[v]) <= set(E[w]) for w in W for v in E[w])
def nested(E):
    for w in W:
        for v in W:
            a, b = set(E[w]), set(E[v])
            if a & b and not (a <= b or b <= a):
                return False
    return True
def s4(E):          return reflexive(E) and transitive(E) and nested(E)
def partitional(E): return all(set(E[v]) == set(E[w]) for w in W for v in E[w])
def refines(A, B):  return all(set(A[w]) <= set(B[w]) for w in W)


# === Recommended strategy = genuine argmax of the OWN posterior (tie-break: option 0) ===
def cond_num(E, j, w):  return sum(pi[u] * O[j][u] for u in E[w])         # numerator
def cond_mass(E, w):    return sum(pi[u] for u in E[w])                   # denominator
def posterior(E, j, w): return cond_num(E, j, w) / cond_mass(E, w)
def rec_opt(E, w):
    # argmax over j of posterior(E,j,w); same cell => argmax of numerator; tie -> 0
    return 1 if cond_num(E, 1, w) > cond_num(E, 0, w) else 0
def value(E):
    return sum(pi[w] * O[rec_opt(E, w)][w] for w in W)


def report():
    print("=== Witness (exactly as in negative-voi.lean) ===")
    for nm, E in [("E1", E1), ("E2", E2), ("Q ", Q)]:
        print(f"  {nm}: cells={ {w: sorted(E[w]) for w in W} }  "
              f"S4={s4(E)}  partitional={partitional(E)}")
    print(f"  E1 refines E2: {refines(E1, E2)}  (strictly finer at w=2: {E1[2] != E2[2]})")
    print(f"  E1 refines Q : {refines(E1, Q)}")
    for nm, E in [("E1", E1), ("E2", E2), ("Q", Q)]:
        ro = [rec_opt(E, w) for w in W]
        print(f"  rec_opt({nm})={ro}  Value({nm})={value(E)}")
    print()
    print("  (i)  NEGATIVE VoI   V(E1) < V(E2) :", value(E1) < value(E2),
          f"  ({value(E1)} < {value(E2)})")
    print("  (ii) NEAR-MISS      V(Q)  <= V(E1):", value(Q) <= value(E1),
          f"  ({value(Q)} <= {value(E1)};  strict: {value(Q) < value(E1)})")
    print("       partitional Q strictly dominated by E2:",
          value(Q) < value(E2), f"  ({value(Q)} < {value(E2)})")
    assert s4(E1) and s4(E2) and s4(Q)
    assert not partitional(E1) and not partitional(E2) and partitional(Q)
    assert refines(E1, E2) and refines(E1, Q)
    assert value(E1) < value(E2)          # strict negative VoI
    assert value(Q) <= value(E1)          # near-miss restores Geanakoplos
    assert value(Q) < value(E2)
    print("  [witness asserts PASS]\n")


# === Exhaustive search: is the negative sign genuinely caused by non-partitionality? ===
def all_experiments():
    choices = []
    for w in W:
        subs = [tuple(i for i in W if mask & (1 << i))
                for mask in range(1, 8) if (mask & (1 << w))]   # reflexive cells
        choices.append(subs)
    for combo in product(*choices):
        yield {w: set(combo[w]) for w in W}


def exhaustive_check():
    """Over all S4 experiments on 3 worlds and all menus in {0,1/2,1}^3 with STRICT argmax
       (no ties, so the tie-break is irrelevant):
       (a) every strict negative-VoI instance V(Ea)<V(Eb), Ea refines Eb, has Eb NON-partitional;
       (b) a refinement of ANY partitional experiment P never loses value: V(Ea) >= V(P).
       Both are the content of Geanakoplos / its tightness."""
    vals = [F(0), F(1, 2), F(1)]
    menus = [[{0: a[0], 1: a[1], 2: a[2]}, {0: b[0], 1: b[1], 2: b[2]}]
             for a in product(vals, repeat=3) for b in product(vals, repeat=3)]
    s4s = [E for E in all_experiments() if s4(E)]
    parts = [E for E in s4s if partitional(E)]
    global O
    saved = O
    n_neg = 0
    violations = 0          # negative VoI with PARTITIONAL coarser expert (should be 0)
    near_miss_failures = 0  # Ea refines partitional P but V(Ea) < V(P) (should be 0)

    def strict_argmax(E):
        return all(cond_num(E, 0, w) != cond_num(E, 1, w) for w in W)

    for Ea in s4s:
        for Eb in s4s:
            if not refines(Ea, Eb):
                continue
            for menu in menus:
                O = menu
                if not (strict_argmax(Ea) and strict_argmax(Eb)):
                    continue
                if value(Ea) < value(Eb):
                    n_neg += 1
                    if partitional(Eb):
                        violations += 1
    for P in parts:
        for Ea in s4s:
            if not refines(Ea, P):
                continue
            for menu in menus:
                O = menu
                if not (strict_argmax(Ea) and strict_argmax(P)):
                    continue
                if value(Ea) < value(P):
                    near_miss_failures += 1
    O = saved
    print("=== Exhaustive search over all 3-world S4 experiments, menus in {0,1/2,1}^3 ===")
    print(f"  strict-argmax negative-VoI instances found:                 {n_neg}")
    print(f"  ...of which the COARSER expert was PARTITIONAL (must be 0):  {violations}")
    print(f"  refinements of a PARTITIONAL expert that LOSE value (must be 0): {near_miss_failures}")
    print("  => negative VoI requires non-partitionality; partitional anchor always restores VoI>=0."
          if violations == 0 and near_miss_failures == 0 else "  => SEARCH FOUND A VIOLATION!")
    assert violations == 0
    assert near_miss_failures == 0


if __name__ == "__main__":
    report()
    exhaustive_check()
    print("\nALL CHECKS PASS.")
