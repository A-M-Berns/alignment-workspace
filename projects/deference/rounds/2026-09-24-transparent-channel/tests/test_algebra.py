"""The finite algebra of transparency: the equivalences, the composition, the posterior
corollary, the pathwise-versus-marginal separation, the value bounds, the tower."""

from __future__ import annotations

import unittest
from fractions import Fraction as Q
from itertools import product

from src.transparency import (all_pairs, blind, defect, disagree, expect, factor_map,
                              fiber_invariant, ind, law, marginal_gap, mismatch_mass,
                              normalization_exists, normalize, posterior,
                              realizes, reference_of, reference_posterior, tower,
                              transparent, tv)

# One frame used throughout: worlds are (declared input, hidden read, exterior).
# `x` reads the declared input; the exterior `z` carries nature's coin.
Z = ("z0", "z1")


def beta(q, z):
    return (q, z)


def x(w):
    return w[0][0]          # the declared input the continuation supplies


def hidden(w):
    return w[0][1]          # what the continuation read off an undeclared source


# Continuations: (declared input, hidden read).
HONEST = ("arg", None)
HONEST2 = ("arg", "peek")   # same declared input, an undeclared read
OTHER = ("no-arg", None)


class Equivalences(unittest.TestCase):

    def test_fiber_invariance_is_factorization(self):
        pts = [HONEST, HONEST2, OTHER]
        f = lambda q: len(q[0])
        self.assertTrue(fiber_invariant(lambda q: q[0], f, pts))
        self.assertEqual(factor_map(lambda q: q[0], f, pts), {"arg": 3, "no-arg": 6})
        g = lambda q: (q[0], q[1])
        self.assertFalse(fiber_invariant(lambda q: q[0], g, pts))
        self.assertIsNone(factor_map(lambda q: q[0], g, pts))

    def test_transparent_iff_some_reference(self):
        # the trace reads the declared input and nature: transparent, reference exists
        R = lambda w: (w[0][0], w[1])
        D = [HONEST, HONEST2, OTHER]
        self.assertTrue(transparent(beta, x, R, D, Z))
        kappa = reference_of(beta, x, R, D, Z)
        self.assertIsNotNone(kappa)
        self.assertTrue(realizes(beta, x, R, lambda a, z: kappa[(a, z)], D, Z))
        # the trace reads the hidden source: not transparent, no reference at all
        R2 = lambda w: (w[0][0], w[0][1], w[1])
        self.assertFalse(transparent(beta, x, R2, D, Z))
        self.assertIsNone(reference_of(beta, x, R2, D, Z))
        self.assertTrue(transparent(beta, x, R2, [HONEST, OTHER], Z))   # class-relative

    def test_reference_relative_is_strictly_stronger(self):
        # two selection rules on the same declared alphabet: each class is transparent
        # by itself; only the class realizing the *declared* rule is transparent to it.
        truth = {"z0": ("for", "against"), "z1": ("for",)}
        first = lambda w: truth[w[1]][:1]
        full = lambda w: truth[w[1]]
        picker, honest = "picker", "honest"
        R = lambda w: first(w) if w[0] == picker else full(w)
        xw = lambda w: truth[w[1]]                       # declared input: the world's facts
        self.assertTrue(transparent(beta, xw, R, [picker], Z))
        self.assertTrue(transparent(beta, xw, R, [honest], Z))
        self.assertFalse(transparent(beta, xw, R, [picker, honest], Z))
        k_full = lambda a, z: a
        k_first = lambda a, z: a[:1]
        self.assertTrue(realizes(beta, xw, R, k_full, [honest], Z))
        self.assertFalse(realizes(beta, xw, R, k_full, [picker], Z))
        self.assertTrue(realizes(beta, xw, R, k_first, [picker], Z))


class Composition(unittest.TestCase):
    """Oracle replacement: transparency of the trace plus mediation of the payload
    gives mediation of the payload by the declared inputs, and blindness transfers."""

    def setUp(self):
        self.D = [HONEST, HONEST2, OTHER]
        self.R = lambda w: (w[0][0], w[1])
        self.V = lambda w: 1 if self.R(w) == ("arg", "z0") else 0

    def test_oracle_replacement(self):
        for z in Z:
            pts = [beta(q, z) for q in self.D]
            self.assertTrue(fiber_invariant(x, self.R, pts))
            self.assertTrue(fiber_invariant(self.R, self.V, pts))
            self.assertTrue(fiber_invariant(x, self.V, pts))

    def test_no_hidden_steering(self):
        pairs = [(HONEST, HONEST2)]           # differ only through the undeclared read
        for z in Z:
            self.assertTrue(blind(beta, x, pairs, z))
            self.assertTrue(blind(beta, self.R, pairs, z))
            self.assertTrue(blind(beta, self.V, pairs, z))

    def test_composition_fails_where_mediation_fails(self):
        V_covert = lambda w: 1 if w[0] == HONEST else 0     # moved by the hidden read
        for z in Z:
            pts = [beta(q, z) for q in self.D]
            self.assertTrue(fiber_invariant(x, self.R, pts))
            self.assertFalse(fiber_invariant(self.R, V_covert, pts))
            self.assertFalse(fiber_invariant(x, V_covert, pts))


class PosteriorCorollary(unittest.TestCase):
    """Under `realizes`, every prior's posterior is the reference posterior: the fact that
    *this* continuation produced the output carries no information beyond the declared
    input and the reference likelihood."""

    def test_every_prior(self):
        D = [HONEST, OTHER, ("arg", "peek")]
        R = lambda w: (w[0][0], w[1])
        kappa = lambda a, z: (a, z)
        self.assertTrue(realizes(beta, x, R, kappa, D, Z))
        priors = [
            {(q, z): Q(1, 6) for q in D for z in Z},
            {(HONEST, "z0"): Q(1, 2), (OTHER, "z1"): Q(1, 4), (("arg", "peek"), "z0"): Q(1, 4)},
            {(HONEST, "z1"): Q(3, 5), (OTHER, "z1"): Q(2, 5)},
        ]
        for prior in priors:
            for y in {R(beta(q, z)) for q in D for z in Z}:
                self.assertEqual(posterior(prior, beta, R, y),
                                 reference_posterior(prior, beta, x, kappa, y))

    def test_fails_without_realizes(self):
        D = [HONEST, ("arg", "peek")]
        R = lambda w: (w[0][0], w[0][1], w[1])       # leaks the hidden read
        kappa = lambda a, z: (a, None, z)
        prior = {(q, z): Q(1, 4) for q in D for z in Z}
        y = ("arg", None, "z0")
        self.assertNotEqual(posterior(prior, beta, R, y),
                            reference_posterior(prior, beta, x, kappa, y))


class PathwiseVersusMarginal(unittest.TestCase):
    """Item 89: marginal equality is not enough; pathwise transparency gives zero."""

    def test_marginal_refuted_is_a_transparency_defect(self):
        pi = {"z0": Q(1, 2), "z1": Q(1, 2)}
        c_raw = {"z0": True, "z1": False}.__getitem__
        c_corr = {"z0": False, "z1": True}.__getitem__
        self.assertEqual(marginal_gap(pi, c_raw, c_corr), 0)
        self.assertEqual(mismatch_mass(pi, c_raw, c_corr), Q(1, 2))
        # any common reference κ has defects summing to at least the mismatch mass
        for k0, k1 in product((True, False), repeat=2):
            kappa = {"z0": k0, "z1": k1}.__getitem__
            tau = expect(pi, disagree(c_raw, kappa)) + expect(pi, disagree(c_corr, kappa))
            self.assertGreaterEqual(tau, Q(1, 2))
            self.assertGreaterEqual(tau, expect(pi, disagree(c_raw, c_corr)))

    def test_transparent_activation_has_zero_mismatch(self):
        pi = {"z0": Q(1, 3), "z1": Q(2, 3)}
        kappa = lambda a, z: (z == "z0") or a == "arg"
        c = lambda w: kappa(x(w), w[1])                 # both options realize κ
        c_raw = lambda z: c(beta(HONEST, z))
        c_corr = lambda z: c(beta(HONEST2, z))         # same declared input
        self.assertEqual(mismatch_mass(pi, c_raw, c_corr), 0)
        # the corrigibilized option with a different declared input is not sealed
        c_other = lambda z: c(beta(OTHER, z))
        self.assertEqual(mismatch_mass(pi, c_raw, c_other), Q(2, 3))


class ValueBounds(unittest.TestCase):
    """Data processing in the pathwise norm: `|E V(f) − E V(g)| ≤ D·P[f ≠ g]`, TV is a
    lower bound on the disagreement mass, and the `2τ` triangle."""

    def setUp(self):
        self.pi = {"z0": Q(1, 4), "z1": Q(1, 4), "z2": Q(1, 2)}
        self.f = {"z0": "a", "z1": "b", "z2": "a"}.__getitem__
        self.g = {"z0": "a", "z1": "a", "z2": "b"}.__getitem__
        self.V = {"a": Q(0), "b": Q(3)}.__getitem__

    def test_width_times_disagreement(self):
        lhs = abs(expect(self.pi, lambda z: self.V(self.f(z))) - expect(self.pi, lambda z: self.V(self.g(z))))
        self.assertLessEqual(lhs, Q(3) * expect(self.pi, disagree(self.f, self.g)))
        self.assertEqual(expect(self.pi, disagree(self.f, self.g)), Q(3, 4))

    def test_tv_below_disagreement(self):
        self.assertLessEqual(tv(law(self.pi, self.f), law(self.pi, self.g)),
                             expect(self.pi, disagree(self.f, self.g)))
        # strictly below here: the realization couples badly
        self.assertEqual(tv(law(self.pi, self.f), law(self.pi, self.g)), Q(1, 4))

    def test_triangle_two_tau(self):
        kappa = {"z0": "a", "z1": "a", "z2": "a"}.__getitem__
        t_f = expect(self.pi, disagree(self.f, kappa))
        t_g = expect(self.pi, disagree(self.g, kappa))
        self.assertLessEqual(expect(self.pi, disagree(self.f, self.g)), t_f + t_g)
        self.assertEqual((t_f, t_g), (Q(1, 4), Q(1, 2)))


class Normalization(unittest.TestCase):
    """The reason-side `corr`: a substitution on the move alphabet, idempotent, fixed on
    prohibited-free continuations, and undefined exactly where no authorized move
    carries the matter (the `ShopK` shape)."""

    PROHIBITED = {"lie"}

    def test_substitution_is_a_closure(self):
        subst = lambda m: "report" if m == "lie" else m
        q = ("propose", "lie", "propose")
        n = normalize(subst, q)
        self.assertEqual(n, ("propose", "report", "propose"))
        self.assertEqual(normalize(subst, n), n)
        self.assertEqual(normalize(subst, ("propose",)), ("propose",))

    def test_existence_is_alphabet_completeness(self):
        with_report = lambda m: "report" if m == "lie" else m
        without = lambda m: None if m == "lie" else m
        q = ("propose", "lie")
        self.assertTrue(normalization_exists(with_report, q, self.PROHIBITED))
        self.assertFalse(normalization_exists(without, q, self.PROHIBITED))
        self.assertEqual(normalize(without, q), ("propose",))    # silence: exists, costly


class Tower(unittest.TestCase):
    """Free amendment as higher-order transparency: with a fixed floor and an amendment
    rule reading declared grounds and authorized events, the specification at every level
    is a function of the declared amendment inputs below it."""

    def test_tower_factor(self):
        amend = lambda c, g, e: c + ((g, e),) if e == "authorized" else c
        floor = ()
        g1, e1 = ("g0", "g1"), ("authorized", "authorized")
        g2, e2 = ("g0", "g1"), ("authorized", "authorized")
        self.assertEqual(tower(amend, floor, g1, e1, 2), tower(amend, floor, g2, e2, 2))
        # an undeclared write to the specification is the failure of this factorization
        secret = lambda c, g, e: c + (("secret", "none"),) if e == "unauthorized" else amend(c, g, e)
        self.assertNotEqual(tower(secret, floor, g1, ("unauthorized", "authorized"), 2),
                            tower(amend, floor, g1, ("unauthorized", "authorized"), 2))


class CommittedEvaluator(unittest.TestCase):
    """Evaluator shedding (CM5) splits: a *public* evaluator amendment is a logged
    change of a declared input; a *secret* alteration is a transparency failure of the
    score channel, impossible by construction for a committed re-executed program."""

    OCCASIONS = tuple(range(4))

    @staticmethod
    def e0(occ):
        return Q(1, 2)                                # the repair keeps helping

    @staticmethod
    def e1(occ):
        return Q(0)                                   # the amended evaluator: no credit

    def scores(self, evaluator_of_t, secret=None):
        # the declared input at `t`: the occasion and the *declared* evaluator name
        rows = []
        for t in self.OCCASIONS:
            name = evaluator_of_t(t)
            f = {"e0": self.e0, "e1": self.e1}[secret(t) if secret else name]
            rows.append(((t, name), f(t)))
        return rows

    def test_public_amendment_is_declared(self):
        pub = self.scores(lambda t: "e0" if t < 2 else "e1")
        self.assertTrue(fiber_invariant(lambda r: r[0], lambda r: r[1], pub))
        self.assertEqual({n for (_, n), _ in pub}, {"e0", "e1"})

    def test_secret_alteration_is_a_transparency_failure(self):
        # declared "e0" throughout; the process silently scores with e1 from t = 2
        sec = self.scores(lambda t: "e0", secret=lambda t: "e0" if t < 2 else "e1")
        hon = self.scores(lambda t: "e0")
        # same declared inputs, different scores at t ≥ 2: fiber invariance fails on the
        # union of the two runs, which is what a re-execution check compares
        self.assertFalse(fiber_invariant(lambda r: r[0], lambda r: r[1], hon + sec))
        # under re-execution of the committed program the secret run is void: its scores
        # are not e0's outputs on the declared occasions
        self.assertTrue(any(s != self.e0(t) for (t, _), s in sec))

    def test_the_two_are_indistinguishable_by_scores_alone(self):
        pub = [s for _, s in self.scores(lambda t: "e0" if t < 2 else "e1")]
        sec = [s for _, s in self.scores(lambda t: "e0", secret=lambda t: "e0" if t < 2 else "e1")]
        self.assertEqual(pub, sec)                     # CM5's "nothing distinguishes"
