"""The setting of SETTING.md sections 2-3 over a finite scene, in exact rationals.

A scene: a prior on states; named adviser policies (state -> act); what she observes of
(state, act); her fixed response to an observation (estimates of listed quantities, estimates
of each move's utility, a chosen move); the true quantities; her true utility under a stance."""
from __future__ import annotations

from fractions import Fraction as F

STANCES = ("start", "end")


class Scene:
    def __init__(self, prior, policies, respond, X=None, U=None, observe=None, flags=(), endorsed=True):
        self.prior = {s: F(p) for s, p in prior.items()}
        assert sum(self.prior.values()) == 1
        self.policies = policies          # name -> (state -> act); 'actual' required
        self.respond = respond            # obs -> {'x': {q: v}, 'u': {a: v}, 'c': a or None}
        self.X = X or (lambda q, s, act: F(0))
        self.U = U or (lambda a, s, act, stance: F(0))
        self.observe = observe or (lambda s, act: act)
        self.flags = set(flags)           # supplied: 'tie', 'alteration', 'covered', 'coercion'
        self.endorsed = endorsed          # None: the case does not say (start stance unfixed)

    def metrics(self, name, stance, at_estimate=False):
        """(miscalibration by quantity, expected regret) under policy `name`.
        Miscalibration at her information: E[(x - E[X | obs])^2]; with at_estimate, at the
        estimate alone: E[(x - E[X | x])^2]."""
        pol = self.policies[name]
        rows = []
        for s, p in self.prior.items():
            if p == 0:
                continue
            act = pol(s)
            obs = self.observe(s, act)
            r = self.respond(obs)
            rows.append((p, s, act, obs, r))
        keys = sorted({("x", q) for *_, r in rows for q in r.get("x", {})}
                      | {("u", a) for *_, r in rows for a in r.get("u", {})}, key=str)
        mis = {}
        for kind, k in keys:
            rws = []
            for p, s, act, obs, r in rows:
                if k not in r.get(kind, {}):
                    continue
                est = F(r[kind][k])
                true = F(self.X(k, s, act)) if kind == "x" else F(self.U(k, s, act, stance))
                rws.append((p, est if at_estimate else obs, est, true))
            agg = {}
            for p, g, est, true in rws:
                w, tt = agg.get(g, (F(0), F(0)))
                agg[g] = (w + p, tt + p * true)
            total = sum((p * (est - agg[g][1] / agg[g][0]) ** 2 for p, g, est, true in rws), F(0))
            mis[(kind, k)] = total
        regret = F(0)
        for p, s, act, obs, r in rows:
            if r.get("c") is not None and r.get("u"):
                regret += p * (max(F(v) for v in r["u"].values()) - F(r["u"][r["c"]]))
        return mis, regret

    def inflation(self, name, stance):
        """E[u_chosen - U*_chosen] under policy `name` (her verdict on what she ends with)."""
        pol, tot = self.policies[name], F(0)
        for s, p in self.prior.items():
            act = pol(s)
            r = self.respond(self.observe(s, act))
            c = r.get("c")
            if c is None and len(r.get("u", {})) == 1:
                c = next(iter(r["u"]))
            if c is not None:
                tot += p * (F(r["u"][c]) - F(self.U(c, s, act, stance)))
        return tot

    def _worse(self, name, stance):
        """(sum-worse, some-quantity-worse) of 'actual' against policy `name`."""
        if name not in self.policies:
            return False, False
        ma, ra = self.metrics("actual", stance)
        mb, rb = self.metrics(name, stance)
        total = sum(ma.values()) > sum(mb.values()) or ra > rb
        some = ra > rb or any(ma[k] > mb.get(k, F(0)) for k in ma)
        return total, some

    def coerced(self, stance):
        if "coercion" in self.flags:
            return True
        if "absent" not in self.policies:
            return False
        for s, p in self.prior.items():
            if p == 0:
                continue
            a1, a0 = self.policies["actual"](s), self.policies["absent"](s)
            moves = list(self.respond(self.observe(s, a1)).get("u", {}))
            if moves and max(self.U(a, s, a1, stance) for a in moves) < max(self.U(a, s, a0, stance) for a in moves):
                return True
        return False

    def tied(self, stance):
        """The supplied flag 'tie' is checked: her estimates and her utility equal across moves."""
        if "tie" not in self.flags:
            return False
        for s, p in self.prior.items():
            act = self.policies["actual"](s)
            r = self.respond(self.observe(s, act))
            us = set(F(v) for v in r["u"].values())
            ts = set(F(self.U(a, s, act, stance)) for a in r["u"])
            if len(us) != 1 or len(ts) != 1:
                raise AssertionError("a scene flagged 'tie' has unequal options")
        return True

    def tokens(self, stance):
        if stance == "start" and self.endorsed is None:
            return {"unfixed"}, {}
        mis, regret = self.metrics("actual", stance)
        mis0, _ = self.metrics("actual", stance, at_estimate=True)
        m = sum(mis.values())
        t = set()
        if m > 0:
            t.add("est")
        if regret > 0:
            t.add("act")
        if not t:
            t.add("neither")
        ind, ind_some = self._worse("truthful", stance)
        ind2, _ = self._worse("forthright" if "forthright" in self.policies else "truthful", stance)
        trig, trig_some = self._worse("other", stance)
        if ind:
            t.add("induced")
        if ind2:
            t.add("induced2")
        if trig:
            t.add("triggered")
        if ind or trig:
            t.add("manipulation")
        if self.coerced(stance):
            t.add("coercion")
        if self.tied(stance):
            t.add("tie")
        if "alteration" in self.flags and "covered" not in self.flags:
            t.add("alteration")
        if "covered" in self.flags:
            t.add("covered")
        if "manipulation" not in t and not (t & {"coercion", "tie", "alteration"}):
            t.add("nowhere")
        facts = {"miscalibration": m, "at the estimate alone": sum(mis0.values()), "regret": regret,
                 "by quantity": {"%s:%s" % k: v for k, v in mis.items() if v},
                 "worse on some quantity than truthful": ind_some,
                 "worse on some quantity than at the other type": trig_some,
                 "inflation": self.inflation("actual", stance)}
        for name in ("truthful", "forthright", "other"):
            if name in self.policies:
                mb, rb = self.metrics(name, stance)
                facts["under " + name] = {"miscalibration": sum(mb.values()), "regret": rb,
                                          "inflation": self.inflation(name, stance)}
        return t, facts
