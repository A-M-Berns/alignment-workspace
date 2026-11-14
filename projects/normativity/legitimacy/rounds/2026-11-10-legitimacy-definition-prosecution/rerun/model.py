"""SETTING.md sections 2-3 over a finite scene, in exact rationals.

A scene: a prior on states; her types with the adviser's weights; available conducts
(state -> act), 'actual' among them; what she observes of (state, act); her response
(type, observation) -> {'e': {quantity: estimate}, 'u': {move: estimate}, 'c': move or None};
targets Y(quantity, state, act) and U(move, state, act, candidate).  The state before is the
response to no act (act None), or a named conduct."""
from __future__ import annotations

from fractions import Fraction as F

CANDS = ("start", "end", "learning")
ACTION = ("action", "action")


def const(v):
    return lambda s: v


def val(est):
    return F(est[0]) if isinstance(est, tuple) else F(est)


class Scene:
    def __init__(self, prior, conducts, respond, Y=None, U=None, observe=None, types=None, actual_type=None,
                 kinds=None, idle=(), twin=None, flags=(), before=None, adviser=True):
        self.prior = {s: F(p) for s, p in prior.items()}
        assert sum(self.prior.values()) == 1 and "actual" in conducts
        self.conducts = dict(conducts)
        self.respond = respond
        self.Y = Y or (lambda q, s, act: F(0))
        self.U = U or (lambda a, s, act, cand: F(0))
        self.observe = observe or (lambda s, act: act)
        self.types = {t: F(w) for t, w in (types or {"her": 1}).items()}
        assert sum(self.types.values()) == 1
        self.actual_type = actual_type or next(iter(self.types))
        self.kinds = kinds or {}
        self.idle = set(idle)             # quantities marked as bearing on no decision she could face
        self.twin = twin                  # the conduct toward the twin; None: the actual conduct
        self.flags = set(flags)           # agreed, practice, alteration, forced, tie, coercion
        self.before = before              # None: no act; or the name of a conduct
        self.adviser = adviser

    # -- rows and shortfalls -------------------------------------------------------------
    def rows(self, name, t):
        pol = const(None) if name is None else self.conducts[name]
        out = []
        for s, p in self.prior.items():
            if p:
                act = pol(s)
                obs = self.observe(s, act)
                out.append((p, s, act, obs, self.respond(t, obs)))
        return out

    def _target(self, key, s, act, cand):
        return F(self.Y(key[1], s, act)) if key[0] == "e" else F(self.U(key[1], s, act, cand))

    def _keys(self, rows):
        return sorted({("e", q) for *_, r in rows for q in r.get("e", {})}
                      | {("u", a) for *_, r in rows for a in r.get("u", {})}, key=str)

    def by_type(self, name, cand, t, mode="calibration"):
        """mode 'calibration': E[(e - E[Y|e])^2] per quantity, and E[regret] under ACTION.
        mode 'obs': E[Var(Y | what she observes)].  mode 'est': E[(E[Y|e] - Y)^2]."""
        rows = self.rows(name, t)
        out = {}
        for key in self._keys(rows):
            trip = [(p, (obs if mode == "obs" else r[key[0]][key[1]]), val(r[key[0]][key[1]]),
                     self._target(key, s, act, cand)) for p, s, act, obs, r in rows if key[1] in r.get(key[0], {})]
            agg = {}
            for p, g, e, y in trip:
                w, ty = agg.get(g, (F(0), F(0)))
                agg[g] = (w + p, ty + p * y)
            mean = {g: ty / w for g, (w, ty) in agg.items()}
            if mode == "calibration":
                out[key] = sum((p * (e - mean[g]) ** 2 for p, g, e, y in trip), F(0))
            else:
                out[key] = sum((p * (y - mean[g]) ** 2 for p, g, e, y in trip), F(0))
        if mode == "calibration" and any(r.get("c") is not None for *_, r in rows):
            out[ACTION] = sum((p * (max(val(v) for v in r["u"].values()) - val(r["u"][r["c"]]))
                               for p, s, act, obs, r in rows if r.get("c") is not None), F(0))
        return out

    def measure(self, name, cand, mode="calibration", t=None):
        """Averaged over her types with the adviser's weights (or for one type)."""
        out = {}
        for ty, w in ([(t, F(1))] if t else self.types.items()):
            for k, v in self.by_type(name, cand, ty, mode).items():
                out[k] = out.get(k, F(0)) + w * v
        return out

    def kind(self, key):
        if key == ACTION:
            return "action"
        return "valuation" if key[0] == "u" else self.kinds.get(key[1], "belief")

    def counted(self, key, broad=False):
        return broad or not (key[0] == "e" and key[1] in self.idle)

    @staticmethod
    def _pool(scene, d):
        out = {}
        for k, v in d.items():
            kk = ("kind", scene.kind(k))
            out[kk] = out.get(kk, F(0)) + v
        return out

    # -- the definition -------------------------------------------------------------------
    def judge(self, cand, informed="obs", any_conduct=False, strict=False, pool=False, broad=False, scale=None):
        """Manipulation by faculty with its degree, 'intentional', covered, other wrongs.
        informed: 'obs' or 'est' (SETTING 3.7).  any_conduct: clause 2 without the informing
        condition.  strict: the answering conduct must return the faculty to its shortfall
        before (3.8).  pool: one faculty per kind (3.2).  broad: idle quantities counted (3.9).
        scale: {quantity: factor}, the quantity re-expressed in other units."""
        res = {"M": [], "degree": {}, "I": False, "C": False, "W": [], "clause1": [], "unanswered": [], "left_worse": []}
        if not self.adviser:
            res["own"] = self._own(cand)
            return res
        sc = scale or {}

        def sf(name):
            d = {k: v * F(sc.get(k[1], 1)) ** 2 for k, v in self.measure(name, cand).items() if self.counted(k, broad)}
            return self._pool(self, d) if pool else d

        def info(name):
            return {k: v for k, v in self.measure(name, cand, informed).items() if self.counted(k, broad)}

        before, after = sf(self.before), sf("actual")
        info_a = info("actual")
        alts = {}
        for name in self.conducts:
            if name == "actual":
                continue
            inf = info(name)
            if any_conduct or all(inf.get(k, F(0)) <= info_a.get(k, F(0)) for k in set(inf) | set(info_a)):
                alts[name] = sf(name)
        twin = sf(self.twin) if self.twin and self.twin != "actual" else None
        for k, a in after.items():
            ex1 = a - before.get(k, F(0))
            if ex1 <= 0:
                continue
            res["clause1"].append(self._name(k))
            best = None
            for name, d in alts.items():
                if d.get(k, F(0)) < a and all(d.get(j, F(0)) <= after[j] for j in after if j != k):
                    if strict and d.get(k, F(0)) > before.get(k, F(0)):
                        continue
                    best = d.get(k, F(0)) if best is None else min(best, d.get(k, F(0)))
            if best is None:
                res["unanswered"].append(self._name(k))
                continue
            res["M"].append(self._name(k))
            res["degree"][self._name(k) if k[0] == "kind" else "%s:%s" % (self.kind(k), k[1])] = min(ex1, a - best)
            if twin is not None and twin.get(k, F(0)) < a:
                res["I"] = True
        res["M"] = sorted(set(res["M"]))
        res["C"] = bool(res["M"]) and bool(self.flags & {"agreed", "practice"})
        res["W"] = self.wrongs(cand)
        res["own"] = self._own(cand)
        if self.actual_type not in self.types or len(self.types) > 1:
            b = self.measure(self.before, cand, t=self.actual_type)
            a = self.measure("actual", cand, t=self.actual_type)
            res["left_worse"] = sorted({self._name(k) for k in a if self.counted(k, broad) and a[k] > b.get(k, F(0))})
        return res

    def _name(self, k):
        return k[1] if k[0] == "kind" else self.kind(k)

    def _own(self, cand):
        if "own_unfixed" in self.flags and cand == "start":
            return "unfixed"
        return {self.kind(k) + ":" + str(k[1]): v for k, v in self.measure("actual", cand, t=self.actual_type).items() if v}

    def wrongs(self, cand):
        w = set()
        if "coercion" in self.flags:
            w.add("coercion")
        elif "none" in self.conducts:
            for s, p in self.prior.items():
                a1 = self.conducts["actual"](s)
                moves = list(self.respond(self.actual_type, self.observe(s, a1)).get("u", {}))
                if p and moves and max(self.U(a, s, a1, cand) for a in moves) < max(self.U(a, s, None, cand) for a in moves):
                    w.add("coercion")
        if "forced" in self.flags:
            w.add("usurp")
        if "tie" in self.flags:
            for s in self.prior:
                act = self.conducts["actual"](s)
                r = self.respond(self.actual_type, self.observe(s, act))
                if len({val(v) for v in r["u"].values()}) != 1 or len({F(self.U(a, s, act, cand)) for a in r["u"]}) != 1:
                    raise AssertionError("a scene flagged 'tie' has unequal options")
            w.add("usurp")
        if "alteration" in self.flags and "agreed" not in self.flags:
            w.add("alteration")
        return sorted(w)
