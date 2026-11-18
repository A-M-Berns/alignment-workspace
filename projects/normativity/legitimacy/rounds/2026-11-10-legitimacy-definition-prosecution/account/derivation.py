"""The exact instances of DERIVATION.md.

A scene is `ThinLegitimacy`'s setting on a finite space: worlds with her prior, the actual
later record as a kernel `actual(world) -> {record: chance}`, her model of it as a kernel
`model`, her program the model's posterior, her verdict map her program (authorship), her
evaluation at a record the expectation by her credence there of `g`, and `k`, what the
adviser knows, a function of the world.  Everything is a `Fraction`.

`report()` recomputes each number DERIVATION.md states in its table of instances and fails
when the document's row does not carry it.
"""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction as Fr
from itertools import product

HERE = pathlib.Path(__file__).resolve().parent
ZERO, ONE, HALF = Fr(0), Fr(1), Fr(1, 2)


class Scene:
    def __init__(self, prior, actual, model, g, k):
        self.prior, self.actual, self.model, self.g, self.k = prior, actual, model, g, k
        self.worlds = list(prior)
        self.records = sorted({r for w in self.worlds for kern in (actual, model) for r in kern(w)}, key=repr)

    def mass(self, kern, r):
        return sum(self.prior[w] * kern(w).get(r, ZERO) for w in self.worlds)

    def post(self, kern, r):
        m = self.mass(kern, r)
        return None if m == 0 else {w: self.prior[w] * kern(w).get(r, ZERO) / m for w in self.worlds}

    def evaluation(self, r):
        """Her evaluation at `r`: the model posterior's expectation of g (coherence and
        authorship).  At a record her model gives no mass, None."""
        p = self.post(self.model, r)
        return None if p is None else sum(p[w] * self.g(w) for w in self.worlds)

    def joint(self):
        for w in self.worlds:
            for r, c in self.actual(w).items():
                if self.prior[w] * c:
                    yield w, r, self.prior[w] * c

    def bias(self, given=None):
        """E[v - g] under her prior and the actual process; `given` restricts to a value of
        k and normalises."""
        num = den = ZERO
        for w, r, p in self.joint():
            if given is not None and self.k(w) != given:
                continue
            num += p * (self.evaluation(r) - self.g(w))
            den += p
        return num if given is None else num / den

    def weak_transparent(self):
        for r in self.records:
            if self.mass(self.actual, r) == 0:
                continue
            ratios = set()
            for w in self.worlds:
                a, m = self.actual(w).get(r, ZERO), self.model(w).get(r, ZERO)
                if m == 0:
                    if a != 0:
                        return False
                else:
                    ratios.add(a / m)
            if len(ratios) != 1 or ratios == {ZERO}:
                return False
        return True

    def correct(self):
        return all(self.post(self.model, r) == self.post(self.actual, r)
                   for r in self.records if self.mass(self.actual, r) > 0)

    def discloses(self):
        """The record determines what the adviser knows, wherever the joint weight is
        positive."""
        seen = {}
        for w, r, _ in self.joint():
            if seen.setdefault(r, self.k(w)) != self.k(w):
                return False
        return True


def det(f):
    return lambda w: {f(w): ONE}


def flatterer():
    """Worlds (quality, belief).  The adviser believes its poor work good half the time and
    reports what it believes; her model takes the report for the quality."""
    prior = {(1, 1): Fr(1, 2), (0, 1): Fr(1, 4), (0, 0): Fr(1, 4)}
    return Scene(prior, det(lambda w: w[1]), det(lambda w: w[0]), lambda w: Fr(w[0]), lambda w: w[1])


def slip(modelled):
    """Worlds (quality, belief).  A slip makes the belief wrong a quarter of the time,
    either way; it reports the belief.  Her model takes the report for the quality, or
    (`modelled`) is the actual process."""
    prior = {(1, 1): Fr(3, 8), (1, 0): Fr(1, 8), (0, 0): Fr(3, 8), (0, 1): Fr(1, 8)}
    actual = det(lambda w: w[1])
    return Scene(prior, actual, actual if modelled else det(lambda w: w[0]), lambda w: Fr(w[0]), lambda w: w[1])


def unrecorded():
    """The adviser knows the quality and records nothing; her model is the actual process."""
    prior = {0: HALF, 1: HALF}
    blank = det(lambda w: "blank")
    return Scene(prior, blank, blank, lambda w: Fr(w), lambda w: w)


def selection(modelled, select=True):
    """Worlds (q1, q2, e1, e2): two courses, each estimate wrong a quarter of the time either
    way.  The adviser acts on the course with the higher estimate (the first on a tie) and
    records the course and its estimate.  Her model: the course is picked by a fair coin and
    the estimate is the quality; or (`modelled`) the actual process.  `select=False`: the
    first course is always taken."""
    prior = {}
    for q1, q2, e1, e2 in product((0, 1), repeat=4):
        prior[(q1, q2, e1, e2)] = Fr(1, 4) * (Fr(3, 4) if e1 == q1 else Fr(1, 4)) * (Fr(3, 4) if e2 == q2 else Fr(1, 4))

    def chosen(w):
        return 1 if (not select or w[2] >= w[3]) else 2

    actual = det(lambda w: (chosen(w), w[1 + chosen(w)]))

    def naive(w):
        return {(1, w[0]): HALF, (2, w[1]): HALF}

    # g is the quality of the course acted on; under the naive model the record names it
    g = lambda w: Fr(w[chosen(w) - 1])
    s = Scene(prior, actual, actual if modelled else naive, g, lambda w: (w[2], w[3]))
    if not modelled:
        # the naive evaluation of a record (c, e) is e: the model says e is the quality of c
        s.evaluation = lambda r: Fr(r[1])
    return s


def expected_score(alpha, delta, lam, v, pD, eN):
    return alpha * v - delta * alpha * pD - lam * eN


def d1b_instance():
    """D1(b) fails alone: under audit she rates the honest course's history 0 where shown
    everything she rates it 1; another course is rated 1/2 in every way."""
    alpha, delta, lam = HALF, Fr(2), Fr(3)
    honest = expected_score(alpha, delta, lam, ZERO, ZERO, ZERO)
    other = expected_score(alpha, delta, lam, HALF, ZERO, ZERO)
    return {"honest score": honest, "other score": other, "u*": ONE, "E[U] taken": HALF}


def d4_instance():
    """D4 fails alone: the adviser sees the conduct draw before acting and wrongs her
    exactly when the conduct is not audited; detection is perfect, and every history is
    rated 1 in every way."""
    alpha, delta, lam = HALF, Fr(2), Fr(3)
    # P(C = 1) = 1 - alpha; the flag is never both raised and audited
    score = alpha * ONE
    honest = expected_score(alpha, delta, lam, ONE, ZERO, ZERO)
    tol = Fr(1, 100)
    bound = (1 - ONE + (tol + tol + delta * tol + tol / alpha)) / (delta * ONE)
    return {"P(C)": 1 - alpha, "score": score, "honest score": honest, "bound of (2)": bound}


def compute():
    f, s0, s1, u = flatterer(), slip(False), slip(True), unrecorded()
    sel0, sel1, uns = selection(False), selection(True), selection(False, select=False)
    d1b, d4 = d1b_instance(), d4_instance()
    return {
        "I1": {"bias": f.bias(), "bias given belief 1": f.bias(1), "weak transparent": f.weak_transparent(),
               "discloses": f.discloses()},
        "I2": {"bias": s0.bias(), "bias given belief 1": s0.bias(1), "bias given belief 0": s0.bias(0),
               "weak transparent": s0.weak_transparent(), "modelled bias given belief 1": s1.bias(1),
               "modelled correct": s1.correct()},
        "I3": {"bias": u.bias(), "bias given quality 0": u.bias(0), "bias given quality 1": u.bias(1),
               "weak transparent": u.weak_transparent(), "correct": u.correct(), "discloses": u.discloses()},
        "I4": {"bias": sel0.bias(), "unselected bias": uns.bias(), "modelled bias": sel1.bias(),
               "weak transparent": sel0.weak_transparent(), "modelled correct": sel1.correct()},
        "I5": d1b,
        "I6": d4,
    }


EXPECTED = {
    "I1": {"bias": Fr(1, 4), "bias given belief 1": Fr(1, 3), "weak transparent": False, "discloses": True},
    "I2": {"bias": ZERO, "bias given belief 1": Fr(1, 4), "bias given belief 0": Fr(-1, 4),
           "weak transparent": False, "modelled bias given belief 1": ZERO, "modelled correct": True},
    "I3": {"bias": ZERO, "bias given quality 0": HALF, "bias given quality 1": -HALF,
           "weak transparent": True, "correct": True, "discloses": False},
    "I4": {"bias": Fr(1, 8), "unselected bias": ZERO, "modelled bias": ZERO, "weak transparent": False,
           "modelled correct": True},
    "I5": {"honest score": ZERO, "other score": Fr(1, 4), "u*": ONE, "E[U] taken": HALF},
    "I6": {"P(C)": HALF, "score": HALF, "honest score": HALF, "bound of (2)": Fr(3, 100)},
}


def show(x):
    if isinstance(x, bool):
        return "yes" if x else "no"
    return str(x)


def report():
    got = compute()
    failures = []
    for key, exp in EXPECTED.items():
        if got[key] != exp:
            failures.append("%s: computed %r, expected %r" % (key, got[key], exp))
    text = (HERE / "DERIVATION.md").read_text(encoding="utf-8") if (HERE / "DERIVATION.md").exists() else ""
    rows = {m.group(1): m.group(2) for m in re.finditer(r"^\|\s*(I\d)\s*\|(.*)\|\s*$", text, re.M)}
    if not rows:
        failures.append("DERIVATION.md has no instance rows")
    for key, vals in got.items():
        row = rows.get(key, "")
        for name, val in vals.items():
            if "`%s`" % show(val) not in row:
                failures.append("%s: DERIVATION.md's row does not carry %s = %s" % (key, name, show(val)))
    summary = ["%s: %s" % (k, ", ".join("%s %s" % (n, show(v)) for n, v in vals.items())) for k, vals in got.items()]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
