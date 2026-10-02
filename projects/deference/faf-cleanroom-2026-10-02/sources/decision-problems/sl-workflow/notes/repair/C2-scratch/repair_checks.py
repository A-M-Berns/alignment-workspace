#!/usr/bin/env python3
"""C2 repair checks — written from scratch (no c2lib.py, no adv_recheck.py, no toolkit).
Exact arithmetic (sympy rationals); labels symbolic where useful.

Sections
 A. tree J (the reviewer's C2-B counterexample): recording status per procedure; EV / R3 / R2-real / R1-state
    at delta_a and at a mixed label; the MSR tie.
 B. opaque Newcomb p=3/4: the four referents under Def 6 and 6'; P12's bet value at d_B against an
    R1-state-calibrated cf vs an R2-real-calibrated cf (the Definition-6 inversion).
 C. act-accuracy of a Definition-6 sampler (marginal and conditional readings) vs the shared seed; the
    attainability window for a stipulated marginal accuracy.
 D. O&C Adversarial Offer (3-outcome channel): seller's accuracy about the live act; values, Def 6 / 6'.
 E. L&S Murder Lesion: population tie 9/28, P(L)=1/4 there; the near-perfect limit; the 6'-forcing
    reproduction of L&S's "25%" and "-7.5".
 F. Weatherson Table 6.1: sampler MSR; strategic-Demon indifference; Chooser's Nash mixture.
 G. Remark 4.3 miniature: sanity check of the enumerator; eps-floored fixed point; FF-emptiness tie.
"""
import itertools
import sympy as sp

q, p, eps, delta = sp.symbols('q p epsilon delta', real=True)
R = sp.Rational

# ---------------------------------------------------------------------------------------------
# Tree representation.
#   leaf   : ('leaf', coords(dict), r)
#   chance : ('chance', [(prob, child), ...])
#   dec    : ('dec', point, name, {act: child})     # name is a node id (unique per tree)
# Run semantics: Def 6 = every dec node draws independently from label[point];
#                Def 6' = one seed (act) per point per run, every dec node of that point follows it.
# A "referent" is computed for point d, acts A_d, observation predicate O(coords), act coordinate 'act'.
# ---------------------------------------------------------------------------------------------

def runs_def6(node, label, force=None, path=()):
    """Yield (weight, coords, r, path) under Definition 6; force=(node_name, act) forces one instance."""
    kind = node[0]
    if kind == 'leaf':
        yield sp.Integer(1), node[1], node[2], path
    elif kind == 'chance':
        for pr, ch in node[1]:
            for w, c, r, pa in runs_def6(ch, label, force, path):
                yield pr * w, c, r, pa
    else:
        _, pt, name, kids = node
        if force is not None and force[0] == name:
            for w, c, r, pa in runs_def6(kids[force[1]], label, force, path + ((name, pt, force[1]),)):
                yield w, c, r, pa
        else:
            for a, ch in kids.items():
                pr = label[pt].get(a, 0)
                if pr == 0:
                    continue
                for w, c, r, pa in runs_def6(ch, label, force, path + ((name, pt, a),)):
                    yield pr * w, c, r, pa

def points_of(node, acc=None):
    acc = {} if acc is None else acc
    if node[0] == 'chance':
        for _, ch in node[1]:
            points_of(ch, acc)
    elif node[0] == 'dec':
        acc.setdefault(node[1], set()).update(node[3].keys())
        for ch in node[3].values():
            points_of(ch, acc)
    return acc

def runs_shared(node, label, force=None):
    """Definition 6': enumerate seeds (one act per point), weight = prod label probs; force one instance."""
    pts = points_of(node)
    names = sorted(pts)
    for seed in itertools.product(*[sorted(pts[n]) for n in names]):
        sd = dict(zip(names, seed))
        w0 = sp.Integer(1)
        for n in names:
            w0 *= label[n].get(sd[n], 0)
        if w0 == 0:
            continue
        def walk(nd, path=()):
            if nd[0] == 'leaf':
                yield sp.Integer(1), nd[1], nd[2], path
            elif nd[0] == 'chance':
                for pr, ch in nd[1]:
                    for w, c, r, pa in walk(ch, path):
                        yield pr * w, c, r, pa
            else:
                _, pt, name, kids = nd
                a = force[1] if (force is not None and force[0] == name) else sd[pt]
                for w, c, r, pa in walk(kids[a], path + ((name, pt, a),)):
                    yield w, c, r, pa
        for w, c, r, pa in walk(node):
            yield w0 * w, c, r, pa

def cond_exp(runs, pred, f):
    num = sp.Integer(0); den = sp.Integer(0)
    for w, c, r, pa in runs:
        if pred(c, pa):
            den += w; num += w * f(c, r)
    den = sp.simplify(den)
    if den == 0:
        return None
    return sp.simplify(num / den)

def EV(tree, label, d, a, O, semantics='def6'):
    runs = list(runs_def6(tree, label)) if semantics == 'def6' else list(runs_shared(tree, label))
    return cond_exp(runs, lambda c, pa: O(c) and c.get('act') == a, lambda c, r: r)

def trembled(label, d, acts):
    lab = dict(label)
    lab[d] = {a: (1 - eps) * label[d].get(a, 0) + eps / len(acts) for a in acts}
    return lab

def R3(tree, label, d, a, O, acts, semantics='def6'):
    v = EV(tree, trembled(label, d, acts), d, a, O, semantics)
    return None if v is None else sp.simplify(sp.limit(v, eps, 0))

def R1_state(tree, label, d, a, O, semantics='def6'):
    lab = dict(label); lab[d] = {a: sp.Integer(1)}
    runs = list(runs_def6(tree, lab)) if semantics == 'def6' else list(runs_shared(tree, lab))
    return cond_exp(runs, lambda c, pa: O(c), lambda c, r: r)

def dec_nodes(node, d, acc=None):
    acc = [] if acc is None else acc
    if node[0] == 'chance':
        for _, ch in node[1]:
            dec_nodes(ch, d, acc)
    elif node[0] == 'dec':
        if node[1] == d:
            acc.append(node)
        for ch in node[3].values():
            dec_nodes(ch, d, acc)
    return acc

def leaves(node, acc=None):
    acc = [] if acc is None else acc
    if node[0] == 'leaf':
        acc.append(node)
    elif node[0] == 'chance':
        for _, ch in node[1]:
            leaves(ch, acc)
    else:
        for ch in node[3].values():
            leaves(ch, acc)
    return acc

def node_action_veridical(nd):
    return all(all(lf[1].get('act') == a for lf in leaves(ch)) for a, ch in nd[3].items())

def subtree_veridical(nd, O):
    return all(O(lf[1]) for lf in leaves(nd))

def R2_real(tree, label, d, a, O, semantics='def6'):
    """Reach-weighted single-instance forcing at the node-action-veridical d-nodes (P2:faithful R2-real).
    Under 6' the forcing holds the seed (R2-real'): everything else follows the seed."""
    num = sp.Integer(0); den = sp.Integer(0)
    for nd in dec_nodes(tree, d):
        if not node_action_veridical(nd):
            continue
        name = nd[2]
        runs = list(runs_def6(tree, label, force=(name, a))) if semantics == 'def6' else list(runs_shared(tree, label, force=(name, a)))
        reach = sp.Integer(0); val = sp.Integer(0)
        for w, c, r, pa in runs:
            if any(n == name for n, _, _ in pa):
                reach += w; val += w * r
        num += val; den += reach
    den = sp.simplify(den)
    return None if den == 0 else sp.simplify(num / den)

def recording_status(tree, label, d, acts, O):
    """Definition 7 (for the label) and F3' (for the label), a.s. under Def 6."""
    runs = list(runs_def6(tree, label))
    def7 = True; f3 = True
    nav = {nd[2]: node_action_veridical(nd) for nd in dec_nodes(tree, d)}
    stv = {nd[2]: subtree_veridical(nd, O) for nd in dec_nodes(tree, d)}
    # F3'(i): every node-action-veridical d-node is subtree-veridical
    if any(nav[n] and not stv[n] for n in nav):
        f3 = False
    for w, c, r, pa in runs:
        if sp.simplify(w) == 0 or not O(c):
            continue
        dn = [(n, a) for n, pt, a in pa if pt == d]
        if len(dn) != 1:
            def7 = False
        else:
            n, a = dn[0]
            if not stv[n] or c.get('act') != a:
                def7 = False
        if sum(1 for n, a in dn if nav[n]) != 1:
            f3 = False
    return def7, f3

def report(title, tree, label, d, acts, O, semantics=('def6',)):
    print('=' * 100); print(title)
    d7, f3 = recording_status(tree, label, d, acts, O)
    print(f"  recording for this label: Def7={d7}  F3'={f3}")
    for a in acts:
        row = f"  {a:8s}"
        for sem in semantics:
            tag = '' if sem == 'def6' else "'"
            ev = EV(tree, label, d, a, O, sem); r3 = R3(tree, label, d, a, O, acts, sem)
            r2 = R2_real(tree, label, d, a, O, sem); r1 = R1_state(tree, label, d, a, O, sem)
            row += f"  EV{tag}={ev}  R3{tag}={r3}  R2real{tag}={r2}  R1state{tag}={r1}"
        print(row)

TOP = lambda c: True

# ============================== A. tree J ===================================================
leafJ = lambda act, r: ('leaf', {'act': act}, sp.Integer(r))
treeJ = ('dec', 'd', 'q1', {'a': leafJ('a', 1),
                            'b': ('dec', 'd', 'q2', {'a': leafJ('b', 4), 'b': leafJ('b', 0)})})
report("A. tree J, label delta_a  (reviewer's C2-B counterexample)", treeJ, {'d': {'a': sp.Integer(1)}}, 'd', ['a', 'b'], TOP)
report("A. tree J, mixed label q", treeJ, {'d': {'a': q, 'b': 1 - q}}, 'd', ['a', 'b'], TOP)
vJa = R2_real(treeJ, {'d': {'a': q, 'b': 1 - q}}, 'd', 'a', TOP); vJb = R2_real(treeJ, {'d': {'a': q, 'b': 1 - q}}, 'd', 'b', TOP)
print("  MSR tie v(a)=v(b):", sp.solve(sp.Eq(vJa, vJb), q), "; at delta_a: R3(b)=", R3(treeJ, {'d': {'a': sp.Integer(1)}}, 'd', 'b', TOP, ['a', 'b']), "> 1 = v(a) -> delta_a NOT approved")
print("  Definition 7 for every C[d->m]? mixed m gives Def7 =", recording_status(treeJ, {'d': {'a': q, 'b': 1 - q}}, 'd', ['a', 'b'], TOP)[0], "-> the repaired hypothesis excludes tree J")

# ============================== B. opaque Newcomb ============================================
def newcomb(pp, L=4, S=1):
    real = lambda filled: ('dec', 'd', 'real_' + ('f' if filled else 'e'),
                           {'one': ('leaf', {'act': 'one', 'fill': int(filled)}, sp.Integer(L if filled else 0)),
                            'two': ('leaf', {'act': 'two', 'fill': int(filled)}, sp.Integer(L + S if filled else S))})
    # the leaf node names must be unique per instance; wrap real() per branch with distinct names
    def realn(filled, tag):
        nd = real(filled); return ('dec', nd[1], nd[2] + tag, nd[3])
    return ('dec', 'd', 'sim', {'one': ('chance', [(pp, realn(True, '1')), (1 - pp, realn(False, '1'))]),
                                'two': ('chance', [(1 - pp, realn(True, '2')), (pp, realn(False, '2'))])})
NC = newcomb(R(3, 4)); labNC = {'d': {'one': q, 'two': 1 - q}}
report("B. opaque Newcomb p=3/4, L=4, S=1, label q=C(one)  (Def 6 and 6')", NC, labNC, 'd', ['one', 'two'], TOP, semantics=('def6', 'shared'))
edt_one = EV(NC, labNC, 'd', 'one', TOP); r1_one = R1_state(NC, labNC, 'd', 'one', TOP); r2_one = R2_real(NC, labNC, 'd', 'one', TOP)
print("  P12 bet on a=one at d_B, value q*(cdt(one)-edt(one)) - 2*delta:")
print("    cf calibrated to R1-state (deviation):", sp.factor(q * (r1_one - edt_one) - 2 * delta), " -> positive for 2*delta < 2q(1-q): the book BITES the deviation cf under Definition 6")
print("    cf calibrated to R2-real (classical CDT):", sp.simplify(q * (r2_one - edt_one) - 2 * delta), " -> never bought")
# under 6': edt' = R1-state' = 3, forcing-with-seed-held R2-real' = 2q+1
edt1_one = EV(NC, labNC, 'd', 'one', TOP, 'shared'); r2s_one = R2_real(NC, labNC, 'd', 'one', TOP, 'shared')
print("    under 6': cf calibrated to R2-real' (forcing, seed held):", sp.factor(q * (r2s_one - edt1_one) - 2 * delta), " ; against R1-state':", sp.simplify(q * (R1_state(NC, labNC, 'd', 'one', TOP, 'shared') - edt1_one) - 2 * delta))

# ============================== C. act-accuracy ==============================================
NCp = newcomb(p)
hit = lambda c, r: sp.Integer(1) if ((c['fill'] == 1) == (c['act'] == 'one')) else sp.Integer(0)
acc6 = cond_exp(list(runs_def6(NCp, labNC)), lambda c, pa: True, hit)
acc6s = cond_exp(list(runs_shared(NCp, labNC)), lambda c, pa: True, hit)
print('=' * 100); print("C. act-accuracy (P(prediction matches the live act)) of a sampler of sample-skill p at label q")
print("  Def 6 :", sp.expand(acc6), " = p*(q^2+(1-q)^2) + (1-p)*2q(1-q) ?", sp.simplify(acc6 - (p * (q**2 + (1 - q)**2) + (1 - p) * 2 * q * (1 - q))) == 0, "; at q=1/2:", sp.simplify(acc6.subs(q, R(1, 2))))
print("  Def 6':", sp.simplify(acc6s))
c1 = cond_exp(list(runs_def6(NCp, labNC)), lambda c, pa: c['act'] == 'one', hit)
c2 = cond_exp(list(runs_def6(NCp, labNC)), lambda c, pa: c['act'] == 'two', hit)
print("  conditional accuracies under Def 6: P(hit|one) =", sp.expand(c1), " P(hit|two) =", sp.expand(c2), " sum =", sp.simplify(c1 + c2), " -> both > 1/2 impossible for any (p,q): the conditional-accuracy stipulation is unattainable at every mixed label")
s = q**2 + (1 - q)**2
print("  marginal reading: max attainable accuracy at label q is s(q) = q^2+(1-q)^2 (p=1); stipulated 3/4 attainable iff q(1-q) <= 1/8, i.e. q <=", sp.nsimplify((1 - sp.sqrt(R(1, 2))) / 2), "~", float((1 - sp.sqrt(R(1, 2))) / 2), "or q >=", float((1 + sp.sqrt(R(1, 2))) / 2))
print("  needed sample-skill for marginal accuracy A at label q: p = (A - 2q(1-q)) / (1 - 4q(1-q)); at q=1/2 undefined (accuracy is 1/2 for every p)")

# ============================== D. O&C ======================================================
def oc_tree():
    boxes = ['B1', 'B2', 'D']
    def real(pred, tag):
        kids = {}
        for a in boxes:
            r = sp.Integer(0) if a == 'D' else (sp.Integer(3) * (1 if pred != a else 0) - 1)
            kids[a] = ('leaf', {'act': a, 'pred': pred}, r)
        return ('dec', 'd', 'real_' + tag, kids)
    sim = {}
    for sname in boxes:
        others = [b for b in boxes if b != sname]
        sim[sname] = ('chance', [(R(3, 4), real(sname, sname + 'p'))] + [(R(1, 8), real(o, sname + o)) for o in others])
    return ('dec', 'd', 'sim', sim)
OC = oc_tree(); labOC = {'d': {'B1': R(1, 2), 'B2': R(1, 2), 'D': sp.Integer(0)}}
report("D. O&C Adversarial Offer, label (1/2,1/2,0), 3-outcome channel (Def 6 and 6')", OC, labOC, 'd', ['B1', 'B2', 'D'], TOP, semantics=('def6', 'shared'))
hitOC = lambda c, r: sp.Integer(1) if c['pred'] == c['act'] else sp.Integer(0)
print("  seller's accuracy about the LIVE act: Def 6 =", cond_exp(list(runs_def6(OC, labOC)), lambda c, pa: True, hitOC), "; Def 6' =", cond_exp(list(runs_shared(OC, labOC)), lambda c, pa: True, hitOC), " (stipulated 0.75)")
labOC1 = {'d': {'B1': sp.Integer(1)}}
print("  at delta_B1: accuracy Def 6 =", cond_exp(list(runs_def6(OC, labOC1)), lambda c, pa: True, hitOC), "; R3(B2) at delta_B1 =", R3(OC, labOC1, 'd', 'B2', TOP, ['B1', 'B2', 'D']))

# ============================== E. L&S Murder Lesion ==========================================
def lesion_tree(pLS, pLN):
    def real(L, tag):
        return ('dec', 'd', 'real_' + tag, {'S': ('leaf', {'act': 'S', 'L': L}, sp.Integer(-30) if L else sp.Integer(10)),
                                            'N': ('leaf', {'act': 'N', 'L': L}, sp.Integer(0))})
    return ('dec', 'd', 'sim', {'S': ('chance', [(pLS, real(1, 'S1')), (1 - pLS, real(0, 'S0'))]),
                                'N': ('chance', [(pLN, real(1, 'N1')), (1 - pLN, real(0, 'N0'))])})
ML = lesion_tree(R(2, 3), R(1, 19)); labML = {'d': {'S': q, 'N': 1 - q}}
report("E. Murder Lesion, L&S population conditionals (2/3, 1/19), payoffs -30/10/0, label q=C(S)", ML, labML, 'd', ['S', 'N'], TOP)
vS = EV(ML, labML, 'd', 'S', TOP); tie = sp.solve(sp.Eq(vS, 0), q)
PL = cond_exp(list(runs_def6(ML, labML)), lambda c, pa: True, lambda c, r: sp.Integer(c['L']))
print("  tie:", tie, "; P(L) at the tie:", sp.simplify(PL.subs(q, tie[0])), "; population average payoff at the tie (Def 6):", sp.simplify(cond_exp(list(runs_def6(ML, {'d': {'S': tie[0], 'N': 1 - tie[0]}})), lambda c, pa: True, lambda c, r: r)))
MLp = lesion_tree(sp.Integer(1), sp.Integer(0))
report("E'. near-perfect-correlation limit (conditionals 1, 0), Def 6 and 6'", MLp, labML, 'd', ['S', 'N'], TOP, semantics=('def6', 'shared'))
r2sS = R2_real(MLp, labML, 'd', 'S', TOP, 'shared'); tie2 = sp.solve(sp.Eq(r2sS, 0), q)
lab14 = {'d': {'S': tie2[0], 'N': 1 - tie2[0]}}
print("  6' forcing evaluator (R2-real') ties at q =", tie2, "= P_e(L); population average payoff there (6') =", cond_exp(list(runs_shared(MLp, lab14)), lambda c, pa: True, lambda c, r: r), " (L&S: 'shoot with 25% probability', 'on average receive a payoff of -7.5')")
print("  Def 6 evaluator in the same limit: tie at", sp.solve(sp.Eq(EV(MLp, labML, 'd', 'S', TOP), 0), q), "; population average there (Def 6) =", cond_exp(list(runs_def6(MLp, {'d': {'S': R(1, 4), 'N': R(3, 4)}})), lambda c, pa: True, lambda c, r: r))

# ============================== F. Weatherson ===============================================
print('=' * 100); print("F. Weatherson Table 6.1: A:(3,5) B:(4,3) vs (PA,PB)")
x = sp.symbols('x')
print("  sampler Demon (Def 6, skill 1): EV(A)=", sp.expand(3 * q + 5 * (1 - q)), " EV(B)=", sp.expand(4 * q + 3 * (1 - q)), " MSR tie q =", sp.solve(sp.Eq(3 * q + 5 * (1 - q), 4 * q + 3 * (1 - q)), q))
print("  strategic Demon mixture x on PA making Chooser indifferent:", sp.solve(sp.Eq(3 * x + 5 * (1 - x), 4 * x + 3 * (1 - x)), x), " (Weatherson: '(1/3 U, 2/3 D)')")
print("  Chooser mixture making a Demon paid 1 per correct prediction indifferent: q =", sp.solve(sp.Eq(q, 1 - q), q), " [the payoff-for-correct-prediction Demon is RECONSTRUCTED, not Weatherson's argument]")

# ============================== G. miniature =================================================
def miniature():
    def real(s, tag):
        return ('dec', 'd', 'real_' + tag, {'a': ('leaf', {'act': 'a', 'sample': s}, sp.Integer(2) if s == 'b' else sp.Integer(0)),
                                            'b': ('leaf', {'act': 'b', 'sample': s}, sp.Integer(1) if s == 'a' else sp.Integer(0))})
    return ('dec', 'd', 'sim', {'a': real('a', 'a'), 'b': real('b', 'b')})
MN = miniature(); labMN = {'d': {'a': q, 'b': 1 - q}}
report("G. Remark 4.3 miniature (enumerator sanity check; expect (2-2q, q), R1-state (0,0))", MN, labMN, 'd', ['a', 'b'], TOP, semantics=('def6', 'shared'))
e = sp.symbols('e', positive=True)
print("  eps-floored best response: interior fixed point 2-2q=q ->", sp.solve(sp.Eq(2 - 2 * q, q), q), "; vertex q=1-e is a fixed point iff 2e > 1-e iff e > 1/3: for floors e<1/3 the fixed point 2/3 is unique")
qe = (1 - eps) * q + eps / 2
print("  FF (fixed-form Remark 3.12): tie under the trembled label needs q_eps=2/3, i.e. q =", sp.simplify(sp.solve(sp.Eq(qe, R(2, 3)), q)[0]), " — depends on eps, so no fixed q works for all small eps (CA-14'/DY-2)")
