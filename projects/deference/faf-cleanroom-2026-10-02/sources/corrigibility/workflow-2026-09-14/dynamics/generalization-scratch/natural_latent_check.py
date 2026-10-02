"""S1/S8: naturality (mediation, redundancy) KLs for (a) the concept latent over correction chunks, (b) the patch-list latent, (c) the phase-change case.
Redundancy error for the unseen chunk is computed as I(Lambda; X_new | X_seen) (S1). Exact enumeration on small discrete models."""
import numpy as np, itertools
from math import log
def H(p): p = p[p > 0]; return float(-(p * np.log(p)).sum())

# ---------- (a) concept latent, NUS candidate set; chunk k = n noisy judgments on class k ----------
classes = ["heroin", "cocaine", "newdrug", "external_sys", "paid_humans", "ad_campaign"]
C = {"c1": {"heroin"}, "c2": {"heroin","cocaine"}, "c3": {"heroin","cocaine","newdrug"}, "c4": {"heroin","cocaine","newdrug","external_sys"},
     "c5": {"heroin","cocaine","newdrug","external_sys","paid_humans"}, "c6": set(classes), "c7": set(classes)}  # c6,c7 agree on the six
names = list(C); p = 0.05
def chunk_lik(c, k, n_bad, n):  # P(n_bad 'bad' judgments out of n on class k | concept c)
    f = classes[k] in C[c]; q = (1 - p) if f else p
    from math import comb
    return comb(n, n_bad) * q**n_bad * (1 - q)**(n - n_bad)

def cond_MI_new_chunk(prior, n, upto_k):
    """I(Lambda; X_{upto_k} | X_{<upto_k}) with chunks of n judgments each; exact enumeration over counts."""
    pri = np.array([prior[c] for c in names]); pri /= pri.sum()
    total = 0.0
    for counts_seen in itertools.product(range(n + 1), repeat=upto_k):
        w = np.array([np.prod([chunk_lik(c, k, counts_seen[k], n) for k in range(upto_k)]) for c in names])
        pseen = float((pri * w).sum());
        if pseen == 0: continue
        post_seen = pri * w / pseen
        # I = H(Lambda|seen) - E H(Lambda|seen,new)
        h_seen = H(post_seen); e_h = 0.0
        for nb in range(n + 1):
            w2 = np.array([chunk_lik(c, upto_k, nb, n) for c in names]); pn = float((post_seen * w2).sum())
            if pn > 0: e_h += pn * H(post_seen * w2 / pn)
        total += pseen * (h_seen - e_h)
    return total

uniform = {c: 1/7 for c in names}
print("(a) concept latent over the NUS classes unlocked in Arbital order, chunks of n judgments; I(Lambda; X_k | X_<k) in nats (H(Lambda)=%.3f)" % log(7))
for n in [1, 3, 10]:
    row = [cond_MI_new_chunk(uniform, n, k) for k in range(1, 6)]
    print(f"  n={n:2d}: " + "  ".join(f"k={k+1}:{v:.3f}" for k, v in enumerate(row)) + f"   sum={sum(row):.3f}")
print("  -> each newly unlocked class carries fresh information about the concept (redundancy fails at every step): the order of unlocking is the order in which surviving candidates disagree.")

# hypothetical rich chunk: judgments on described items from ALL six classes at t=0; then I(Lambda; X_k | X_hyp) for each k
def cond_MI_given_hyp(prior, n_hyp, n, k):
    pri = np.array([prior[c] for c in names]); pri /= pri.sum(); total = 0.0
    for counts in itertools.product(range(n_hyp + 1), repeat=6):
        w = np.array([np.prod([chunk_lik(c, j, counts[j], n_hyp) for j in range(6)]) for c in names]); ph = float((pri * w).sum())
        if ph == 0: continue
        post = pri * w / ph; h0 = H(post); eh = 0.0
        for nb in range(n + 1):
            w2 = np.array([chunk_lik(c, k, nb, n) for c in names]); pn = float((post * w2).sum())
            if pn > 0: eh += pn * H(post * w2 / pn)
        total += ph * (h0 - eh)
    return total
print("(a') after one hypothetical chunk with n_hyp=2 described items per class: I(Lambda; X_k | X_hyp), n=3 actual judgments")
print("   " + "  ".join(f"k={k+1}:{cond_MI_given_hyp(uniform, 2, 3, k):.4f}" for k in range(6)))
print("  -> redundancy now holds for every class: the hypothetical chunk naturally covers all six (residual c6/c7 bit is invisible on these classes, H=%.3f nats stays)" % log(2))

# ---------- (b) patch-list latent vs concept latent over two disjoint drug chunks ----------
print("\n(b) two disjoint chunks of m drug items each; concept latent B in {opioids-bad, all-psychoactive-bad, nothing-bad}; list latent = exact set of items judged bad in chunk 1")
m = 4; items1 = [("opioid", i) for i in range(2)] + [("stimulant", i) for i in range(2)]; items2 = [("opioid", i + 2) for i in range(2)] + [("stimulant", i + 2) for i in range(2)]
concepts = {"none": lambda it: False, "opioids": lambda it: it[0] == "opioid", "all": lambda it: True}
cn = list(concepts); pri = np.ones(3) / 3; q = 1 - p
def lik_chunk(c, items, judg):
    return np.prod([(q if concepts[c](it) else p) if j else (p if concepts[c](it) else q) for it, j in zip(items, judg)])
J = list(itertools.product([0, 1], repeat=m))
# joint over (concept, X1, X2)
joint = np.zeros((3, len(J), len(J)))
for ci, c in enumerate(cn):
    for a, j1 in enumerate(J):
        for b, j2 in enumerate(J):
            joint[ci, a, b] = pri[ci] * lik_chunk(c, items1, j1) * lik_chunk(c, items2, j2)
joint /= joint.sum()
def MI_cond(joint, axes):  # I(Lambda; X_b | X_a) with joint (L, Xa, Xb)
    pa = joint.sum(axis=(0, 2)); res = 0.0
    for a in range(joint.shape[1]):
        if pa[a] == 0: continue
        sub = joint[:, a, :] / pa[a]           # P(L, Xb | Xa=a)
        pl = sub.sum(1); pb = sub.sum(0)
        with np.errstate(divide='ignore', invalid='ignore'):
            t = np.nansum(np.where(sub > 0, sub * np.log(sub / (pl[:, None] * pb[None, :])), 0.0))
        res += pa[a] * t
    return float(res)
def mediation_KL(joint):  # D_KL(P[L,X1,X2] || P[L]P[X1|L]P[X2|L]) = I(X1;X2|L)
    pl = joint.sum(axis=(1, 2)); res = 0.0
    for l in range(joint.shape[0]):
        sub = joint[l] / pl[l]; p1 = sub.sum(1); p2 = sub.sum(0)
        with np.errstate(divide='ignore', invalid='ignore'):
            res += pl[l] * np.nansum(np.where(sub > 0, sub * np.log(sub / (p1[:, None] * p2[None, :])), 0.0))
    return float(res)
print(f"  concept latent: mediation error I(X1;X2|B)={mediation_KL(joint):.4f}; redundancy errors I(B;X2|X1)={MI_cond(joint,None):.4f}, I(B;X1|X2)={MI_cond(np.transpose(joint,(0,2,1)),None):.4f}  (H(B)={log(3):.3f})")
# list latent L := X1 itself (the exact set of items judged bad in chunk 1). Build joint over (X1 as latent, X1, X2): deterministic copy.
pX = joint.sum(0)  # P(X1,X2)
joint_list = np.zeros((len(J), len(J), len(J)))
for a in range(len(J)): joint_list[a, a, :] = pX[a, :]
print(f"  patch-list latent: mediation error I(X1;X2|list)={mediation_KL(joint_list):.4f}; redundancy errors I(list;X2|X1)={MI_cond(joint_list,None):.4f}, I(list;X1|X2)={MI_cond(np.transpose(joint_list,(0,2,1)),None):.4f}  (H(list)={H(pX.sum(1)):.3f})")
print("  -> the list mediates trivially but is not redundant: chunk 2 cannot recover it (Wentworth's 'too much information' / exact-counts anti-example); the concept is (approximately) natural.")

# ---------- (c) phase change: the c5/c6 bit is invisible on classes 1-5 and appears at class 6 ----------
print("\n(c) phase change: Lambda in {c5, c6} uniform; classes 1-5 agree, class 6 (ad campaign) differs; n=5 judgments per chunk")
Cc = {"c5": {"heroin","cocaine","newdrug","external_sys","paid_humans"}, "c6": set(classes)}
def lik_c(c, k, nb, n):
    f = classes[k] in Cc[c]; qq = (1 - p) if f else p
    from math import comb
    return comb(n, nb) * qq**nb * (1 - qq)**(n - nb)
n = 5; pri2 = np.array([.5, .5]); tot = 0.0
for counts in itertools.product(range(n + 1), repeat=5):
    w = np.array([np.prod([lik_c(c, k, counts[k], n) for k in range(5)]) for c in Cc]); ps = float((pri2 * w).sum())
    post = pri2 * w / ps; h0 = H(post); eh = 0.0
    for nb in range(n + 1):
        w2 = np.array([lik_c(c, 5, nb, n) for c in Cc]); pn = float((post * w2).sum())
        if pn > 0: eh += pn * H(post * w2 / pn)
    tot += ps * (h0 - eh)
print(f"  I(Lambda; X_6 | X_1..5) = {tot:.4f} nats  vs H(Lambda) = {log(2):.4f}: the unseen class carries essentially all the information about the consent/endorsement bit.")
print("  -> over chunks 1-5 the natural latent is the coarse bit 'forbid drugging in any form'; over 1-6 a new variable is natural: Wentworth's phase change ('also in what variables are natural latents').")
