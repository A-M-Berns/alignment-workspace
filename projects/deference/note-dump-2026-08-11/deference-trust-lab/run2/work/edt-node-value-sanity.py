#!/usr/bin/env python3
"""
Independent sanity-check of edt-node-value.lean (NOT a substitute for the kernel check —
a redundant enumeration so a reader can see the arithmetic and that kappa is load-bearing).

Mirrors the two Lean instances:
  Decoupled.*  : separable U, decoupled kappa -> EDT-argmax attains the global optimum.
  Mugging.*    : NON-separable U (matched-pay reward), severing kappa -> EDT-argmax (at BOTH
                 nodes) STRICTLY misses the UNRESTRICTED global UDT optimum; correlated kappa agrees.
"""
import itertools

A = [0, 1]  # 0 = refuse, 1 = pay
POLICIES = list(itertools.product(A, A))  # all S2->A2 with S2 = {0,1}

def update(base, s, a):
    p = list(base); p[s] = a; return tuple(p)

def argmax_node(vnode, s):
    return max(A, key=lambda a: vnode(s, a))

def report(name, U, kappa, sep_label):
    print(f"=== {name} ({sep_label}) ===")
    for pi in POLICIES:
        print(f"   U{pi} = {U(pi)}")
    glob = max(POLICIES, key=U)
    print(f"   UNRESTRICTED global optimum: {glob}  U={U(glob)}")
    vnode = lambda s, a: U(kappa(s, a))
    pstar = tuple(argmax_node(vnode, s) for s in (0, 1))
    print(f"   vNode table: " + ", ".join(f"v({s},{a})={vnode(s,a)}" for s in (0,1) for a in A))
    print(f"   EDT-argmax policy (BOTH nodes): {pstar}  U={U(pstar)}")
    attains = U(pstar) == U(glob)
    print(f"   EDT-argmax attains global optimum? {attains}   gap = {U(glob)-U(pstar)}")
    return pstar, glob, vnode

# ---- separability test (interaction term) -------------------------------------------------
def interaction(U):
    return U((0,0)) + U((1,1)) - U((0,1)) - U((1,0))

# ---- DECOUPLED instance (mirrors Decoupled.* ; p=1, u below, base=allRefuse) --------------
def u_dec(s, a):
    if s == 0: return 3 if a == 1 else 1
    else:      return 4 if a == 0 else 2
def U_dec(pi):  # separable: sum_s u_s(pi_s)
    return u_dec(0, pi[0]) + u_dec(1, pi[1])
kappa_dec = lambda s, a: update((0, 0), s, a)
print("interaction(U_dec) =", interaction(U_dec), "(0 => separable, as expected)\n")
ps_dec, gl_dec, _ = report("Decoupled", U_dec, kappa_dec, "separable")
assert interaction(U_dec) == 0
assert U_dec(ps_dec) == U_dec(gl_dec), "decoupled: EDT-argmax must attain global optimum"
assert U_dec(gl_dec) == 7 and U_dec((0,0)) == 5
print()

# ---- MUGGING instance (mirrors Mugging.* ; NON-separable matched-pay reward) ---------------
def U_mug(pi):
    own = -100 if pi[0] == 1 else 0
    twin = 10000 if (pi[0] == 1 and pi[1] == 1) else 0   # acausal: fires only on matched-pay
    return own + twin
kappa_sev  = lambda s, a: update((0, 0), s, a)   # severing: other node frozen at refuse
kappa_corr = lambda s, a: (a, a)                 # correlated: twin copies action
print("interaction(U_mug) =", interaction(U_mug), "(!=0 => NON-separable, as required)\n")
ps_sev, gl_mug, vnode_sev = report("Mugging / severing kappa", U_mug, kappa_sev, "NON-separable")
assert interaction(U_mug) != 0, "mugging U must be non-separable"
assert U_mug(gl_mug) == 9900 and gl_mug == (1, 1), "unrestricted optimum must be (pay,pay)=9900"
assert ps_sev == (0, 0), "severing-kappa EDT-argmax must be (refuse,refuse)"
assert U_mug(ps_sev) < U_mug(gl_mug), "DIVERGENCE: EDT-argmax must strictly miss the optimum"
print(f"   gap_is_acausal_payoff: U(glob)-U(edt) = {U_mug(gl_mug)-U_mug(ps_sev)} ; "
      f"severed reward U(glob)-vNode(0,pay) = {U_mug(gl_mug) - vnode_sev(0,1)}")
assert U_mug(gl_mug) - U_mug(ps_sev) == 9900
assert U_mug(gl_mug) - vnode_sev(0, 1) == 10000
print()
ps_corr, gl_corr, _ = report("Mugging / correlated kappa", U_mug, kappa_corr, "NON-separable")
assert U_mug(ps_corr) == U_mug(gl_corr), "correlated kappa must AGREE with the optimum"
print()

# ---- kappa load-bearing: severing vs correlated give DIFFERENT argmaxes for the SAME U -----
print("LOAD-BEARING: same U, severing-kappa argmax =", ps_sev,
      "vs correlated-kappa argmax =", ps_corr,
      "-> DIFFERENT" if ps_sev != ps_corr else "-> SAME (would mean kappa inert!)")
assert ps_sev != ps_corr, "kappa must change the EDT-argmax (else it is inert)"

print("\nALL SANITY CHECKS PASSED.")
