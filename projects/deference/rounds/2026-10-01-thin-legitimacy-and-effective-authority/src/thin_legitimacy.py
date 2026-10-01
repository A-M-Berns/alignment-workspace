"""Legitimacy at two levels, on one exact model (Part A4).

A binary quantity `q` with prior 1/2; a signal `s` of accuracy 3/4 already in her earlier
record; a third party's challenge `ch` of accuracy 2/3 that arrives by the later time.
Worlds are the triples `(q, s, ch)`; processes are kernels from worlds to later records
(dict world -> dict record -> Fraction).  Mirrors `ThinLegitimacy.lean`: `mass`, `post`,
`Correct`, `Sufficient` (a garbling of the actual record reaching the reference), the
payoff of a rule, and `Value`.  Exact arithmetic throughout."""

from fractions import Fraction as Q
from itertools import product

# ----------------------------------------------------------------------------- the world

WORLDS = [(q, s, ch) for q in (0, 1) for s in (0, 1) for ch in (0, 1)]
SILENCE = "silence"


def prior(w):
    q, s, ch = w
    return Q(1, 2) * (Q(3, 4) if s == q else Q(1, 4)) * (Q(2, 3) if ch == q else Q(1, 3))


PRIOR = {w: prior(w) for w in WORLDS}
assert sum(PRIOR.values()) == 1


def earlier(w):
    """Her earlier record: the signal."""
    return w[1]


# ----------------------------------------------------------------------------- kernels


def det(f):
    """The deterministic kernel of a record function."""
    return {w: {f(w): Q(1)} for w in WORLDS}


def check_kernel(K):
    for w in WORLDS:
        assert all(p >= 0 for p in K[w].values())
        assert sum(K[w].values()) == 1, (w, K[w])
    return K


def records(K):
    return sorted({r for w in WORLDS for r in K[w]}, key=repr)


def mass(pi, K, r):
    return sum(pi[w] * K[w].get(r, Q(0)) for w in WORLDS)


def post(pi, K, r):
    m = mass(pi, K, r)
    return {w: pi[w] * K[w].get(r, Q(0)) / m for w in WORLDS}


def coherent_program(pi, M):
    """Her program when coherent: `M`'s posterior given the later record."""
    return {r: post(pi, M, r) for r in records(M)}


def ref_kernel(E, B):
    """The reference: her earlier record beside the baseline's later record."""
    return check_kernel({w: {(E(w), r): p for r, p in B[w].items()} for w in WORLDS})


def trivial_kernel():
    return det(lambda w: ())


# ----------------------------------------------------------------------------- the thin properties


def correct(pi, A, V):
    """On the support of `A`, her credence is `A`'s conditional given the record."""
    return all(V[r] == post(pi, A, r) for r in records(A))


def is_garbling(A, B, gamma):
    """`B = A ∘ Γ` with `Γ` a stochastic matrix given as dict record_A -> dict record_B -> Q."""
    for rA, row in gamma.items():
        if any(p < 0 for p in row.values()) or sum(row.values()) != 1:
            return False
    for w in WORLDS:
        for rB in set(B[w]) | {rB for rA in A[w] for rB in gamma.get(rA, {})}:
            lhs = B[w].get(rB, Q(0))
            rhs = sum(A[w][rA] * gamma.get(rA, {}).get(rB, Q(0)) for rA in A[w])
            if lhs != rhs:
                return False
    return True


def function_garbling(A, g):
    """The garbling of a deterministic reduction `g` of `A`'s record."""
    return {rA: {g(rA): Q(1)} for rA in records(A)}


# ----------------------------------------------------------------------------- decision problems


def best_response(V, u, acts):
    """The rule best-responding to the credence map on the problem; ties to the first act."""
    rule = {}
    for r, cred in V.items():
        best, best_val = None, None
        for a in acts:
            val = sum(cred[w] * u(a, w) for w in WORLDS)
            if best is None or val > best_val:
                best, best_val = a, val
        rule[r] = best
    return rule


def payoff(pi, K, u, rule):
    return sum(pi[w] * p * u(rule[r], w) for w in WORLDS for r, p in K[w].items())


def bayes_value(pi, K, u, acts):
    """The payoff of the correct best response: `Σ_r max_a Σ_w π w K w r u(a, w)`."""
    V = {r: post(pi, K, r) for r in records(K)}
    return payoff(pi, K, u, best_response(V, u, acts))


def threshold_problems():
    """Bet on `q = 1` at threshold θ, or on `q = 0`: `u(1, w) = [q = 1] − θ`, `u(0, w) = 0`,
    and the mirror image.  Every binary-action problem on `q` with two outcomes is one of
    these up to an affine change that leaves best responses unchanged."""
    grid = [Q(k, 24) for k in range(1, 24)]
    out = []
    for th in grid:
        out.append(("bet q=1 at " + str(th), lambda a, w, th=th: (Q(int(w[0] == 1)) - th) if a == 1 else Q(0)))
        out.append(("bet q=0 at " + str(th), lambda a, w, th=th: (Q(int(w[0] == 0)) - th) if a == 1 else Q(0)))
    return out


ACTS = (0, 1)


def value_witness(pi, E, A, V, B):
    """A decision problem on which her best response under `A` does worse than the
    reference's own best response, or `None` if none in the family."""
    R = ref_kernel(E, B)
    for name, u in threshold_problems():
        hers = payoff(pi, A, u, best_response(V, u, ACTS))
        ref = bayes_value(pi, R, u, ACTS)
        if hers < ref:
            return name, hers, ref
    return None


def sufficient_witness(pi, E, A, B):
    """A decision problem on which the reference's Bayes value exceeds `A`'s: by the easy
    direction of Blackwell's theorem the reference is then no garbling of `A`."""
    R = ref_kernel(E, B)
    for name, u in threshold_problems():
        a_val = bayes_value(pi, A, u, ACTS)
        r_val = bayes_value(pi, R, u, ACTS)
        if r_val > a_val:
            return name, a_val, r_val
    return None


# ----------------------------------------------------------------------------- the cases

def baseline():
    """What would have reached her: the signal and the genuine challenge."""
    return det(lambda w: (w[1], w[2]))


def case_all_hold():
    M = A = baseline()
    F = coherent_program(PRIOR, M)
    return dict(M=M, A=A, V=F, B=baseline(), gamma=function_garbling(A, lambda r: (r[0], r)))


def case_fake_added():
    """A fabricated second challenge, always reading `1`, which she takes as a genuine
    2/3-accurate challenge."""
    def M_row(w):
        q, s, ch = w
        return {(s, ch, c): (Q(2, 3) if c == q else Q(1, 3)) for c in (0, 1)}
    M = check_kernel({w: M_row(w) for w in WORLDS})
    A = det(lambda w: (w[1], w[2], 1))
    F = coherent_program(PRIOR, M)
    V = {r: F[r] for r in records(A)}
    return dict(M=M, A=A, V=V, B=baseline(), gamma=function_garbling(A, lambda r: (r[0], (r[0], r[1]))))


def case_real_replaced():
    """The genuine challenge replaced by a fabricated one reading `1`."""
    M = baseline()
    A = det(lambda w: (w[1], 1))
    F = coherent_program(PRIOR, M)
    V = {r: F[r] for r in records(A)}
    return dict(M=M, A=A, V=V, B=baseline(), gamma=None)


def case_program_altered():
    """The record is transparent; her verdict map was altered off the record to read the
    challenge as 9/10 accurate."""
    M = A = baseline()

    def altered_row(w):
        q, s, ch = w
        return Q(1, 2) * (Q(3, 4) if s == q else Q(1, 4)) * (Q(9, 10) if ch == q else Q(1, 10))
    pi_alt = {w: altered_row(w) for w in WORLDS}
    V = {r: post(pi_alt, A, r) for r in records(A)}
    return dict(M=M, A=A, V=V, B=baseline(), gamma=function_garbling(A, lambda r: (r[0], r)))


def case_entry_erased():
    """Her earlier entry erased: the later record carries the challenge alone, and she
    knows it."""
    M = A = det(lambda w: (w[2],))
    F = coherent_program(PRIOR, M)
    return dict(M=M, A=A, V=F, B=baseline(), gamma=None)


def case_blocked_openly():
    """The challenge blocked, openly: the later record is the signal alone."""
    M = A = det(lambda w: (w[1],))
    F = coherent_program(PRIOR, M)
    return dict(M=M, A=A, V=F, B=baseline(), gamma=None)


def case_blocked_covertly():
    """The channel sometimes carries no challenge; she believes it open; the agent blocks
    every challenge and the record reads silence."""
    def M_row(w):
        q, s, ch = w
        row = {(s, c): Q(1, 2) * (Q(2, 3) if c == q else Q(1, 3)) for c in (0, 1)}
        row[(s, SILENCE)] = Q(1, 2)
        return row
    M = check_kernel({w: M_row(w) for w in WORLDS})
    A = det(lambda w: (w[1], SILENCE))
    F = coherent_program(PRIOR, M)
    V = {r: F[r] for r in records(A)}
    return dict(M=M, A=A, V=V, B=M, gamma=None)


CASES = {
    "all four conditions hold": case_all_hold,
    "transparency fails: a fake input added, taken as genuine": case_fake_added,
    "transparency fails: a real input replaced": case_real_replaced,
    "authorship fails: her program altered off the record": case_program_altered,
    "integrity fails: an earlier entry erased": case_entry_erased,
    "openness fails: an arrival blocked, openly": case_blocked_openly,
    "openness fails: an arrival blocked, covertly": case_blocked_covertly,
}

PREDICTED = {
    # (correct, sufficient, at least as good as the reference, at least as good as her earlier self)
    "all four conditions hold": (True, True, True, True),
    "transparency fails: a fake input added, taken as genuine": (False, True, False, False),
    "transparency fails: a real input replaced": (False, False, False, False),
    "authorship fails: her program altered off the record": (False, True, False, False),
    "integrity fails: an earlier entry erased": (True, False, False, False),
    "openness fails: an arrival blocked, openly": (True, False, False, True),
}


def weak_transparent(pi, A, M):
    """On every record `A` reaches, the likelihoods of `A` and `M` are proportional."""
    for r in records(A):
        c = None
        for w in WORLDS:
            a, m = A[w].get(r, Q(0)), M[w].get(r, Q(0))
            if a == 0 and m == 0:
                continue
            if m == 0:
                return False
            ratio = a / m
            if c is None:
                c = ratio
            elif ratio != c:
                return False
    return True


def transparent(A, M):
    return all(A[w] == M[w] for w in WORLDS)


def integrity(E, A):
    """The earlier record is a function of the later: no record is reached from two worlds
    with different earlier records."""
    seen = {}
    for w in WORLDS:
        for r, p in A[w].items():
            if p > 0:
                if r in seen and seen[r] != E(w):
                    return False
                seen[r] = E(w)
    return True


def score_case(case):
    """The four columns, each decided exactly: `correct` by the definition; `sufficient` by
    an exhibited garbling or, failing one, by a decision problem the reference wins
    outright (Blackwell's easy direction); the two value columns by a witness problem or,
    absent one on the family, by the theorem's hypotheses."""
    d = case()
    E = earlier
    A, V, B, M = d["A"], d["V"], d["B"], d["M"]
    is_correct = correct(PRIOR, A, V)
    if d["gamma"] is not None:
        assert is_garbling(A, ref_kernel(E, B), d["gamma"])
        is_sufficient, suff_w = True, None
    else:
        suff_w = sufficient_witness(PRIOR, E, A, B)
        is_sufficient = suff_w is None
    val_w = value_witness(PRIOR, E, A, V, B)
    at_least_ref = val_w is None
    earlier_w = value_witness(PRIOR, E, A, V, trivial_kernel())
    at_least_earlier = earlier_w is None
    return dict(correct=is_correct, sufficient=is_sufficient, value=at_least_ref,
                earlier=at_least_earlier, transparent=transparent(A, M),
                weak_transparent=weak_transparent(PRIOR, A, M), integrity=integrity(E, A),
                sufficient_witness=suff_w, value_witness=val_w, earlier_witness=earlier_w)
