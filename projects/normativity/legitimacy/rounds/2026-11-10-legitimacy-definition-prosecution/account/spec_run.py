"""The statement of STATEMENT.md computed on specifications in the format of SPEC_FORMAT.md.
Exact rationals.  For each specification: lines 1, 2 and 3, the inducing test, whether the
act lowers what her options are worth or what she can know, and the verdict of STATEMENT.md
section 9.7, in the E[.] setting and in the bare setting (section 9.9), at each tolerance.

  python3 -m account.spec_run                 the executor's specifications, summary
  python3 -m account.spec_run --write         rewrite the computed blocks of SPEC_RESULTS.md
  python3 -m account.spec_run --specs FILE    any file of specifications, as a table
"""
from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
DELTAS = (F(0), F(1, 20), F(1, 10), F(1, 4))
REF = ("E", F(1, 10))
SETTINGS = ("E", "bare")


class Bad(Exception):
    pass


# ---------------------------------------------------------------- reading a specification

def fr(x):
    try:
        return F(str(x))
    except (ValueError, ZeroDivisionError) as e:
        raise Bad("not a number: %r" % (x,)) from e


def per_state(d, s):
    if s in d:
        return d[s]
    if "*" in d:
        return d["*"]
    raise Bad("no entry for state %s" % s)


class Spec:
    def __init__(self, raw):
        self.raw = raw
        self.id = raw["id"]
        self.variant = raw.get("variant", "a")
        self.p = {s: fr(v) for s, v in raw["states"].items()}
        if sum(self.p.values()) != 1:
            raise Bad("chances sum to %s" % sum(self.p.values()))
        self.states = [s for s in self.p if self.p[s] > 0]
        self.options = list(raw["options"])
        self.now = {k: (None if v is None else fr(v)) for k, v in raw["futures"].items()}
        self.facts = {f: {s: fr(v) for s, v in by.items()} for f, by in raw.get("facts", {}).items()}
        self.pol = raw["policies"]
        if len(self.pol) < 4:
            raise Bad("fewer than four policies")
        for k in ("actual", "nu", "absent"):
            if raw[k] not in self.pol:
                raise Bad("%s names no policy: %s" % (k, raw[k]))
        self.actual, self.nu, self.absent = raw["actual"], raw["nu"], raw["absent"]
        things = None
        for name in self.pol:
            for s in self.states:
                for o, fut in self.outcome(name, s).items():
                    if o not in self.options:
                        raise Bad("%s: unknown option %s" % (name, o))
                    if fut is not None and fut not in self.now:
                        raise Bad("%s: unknown future %s" % (name, fut))
                keys = [tuple(sorted(t)) for t in self.later(name, s)]
                if things is None:
                    things = keys
                elif keys != things:
                    raise Bad("%s: later valuing rates other things than the first policy's" % name)
                if not [o for o in self.options if self.open(name, s, o)]:
                    raise Bad("%s: no option open in %s" % (name, s))
        for lab, sts in ((lab, sts) for name in self.pol for lab, sts in self.cells(name).items()):
            pass
        for left, rel, right, _ in raw.get("order", []):
            a, b = self.lookup(left), self.lookup(right)
            ok = {"<": a < b, "<=": a <= b, "=": a == b, ">=": a >= b, ">": a > b}[rel]
            if not ok:
                raise Bad("its own order constraint fails: %s %s %s" % (left, rel, right))

    # -- accessors
    def outcome(self, name, s):
        return per_state(self.pol[name]["outcome"], s)

    def open(self, name, s, o):
        return self.outcome(name, s).get(o) is not None

    def obs(self, name, s):
        return self.pol[name].get("obs", {}).get(s, "o")

    def cells(self, name):
        c = {}
        for s in self.states:
            c.setdefault(self.obs(name, s), []).append(s)
        return c

    def later(self, name, s, seen=()):
        lat = self.pol[name]["later"]
        if isinstance(lat, str):
            other = lat.split(":", 1)[1]
            if other not in self.pol or other in seen:
                raise Bad("%s: bad later reference %s" % (name, lat))
            return self.later(other, s, seen + (name,))
        return [{k: fr(v) for k, v in t.items()} for t in per_state(lat, s)]

    def gain(self, name, s, o):
        g = self.pol[name].get("gain", "0")
        if isinstance(g, dict):
            return fr(per_state(g, s).get(o, 0))
        return fr(g)

    def U(self, name, s, o):
        """Her informed rating, at the moment of the act, of the future option o leads to."""
        fut = self.outcome(name, s).get(o)
        return None if fut is None else self.now[fut]

    def lookup(self, path):
        k = path.split(".")
        try:
            if k[0] == "p":
                return self.p[k[1]]
            if k[0] == "now":
                v = self.now[".".join(k[1:])]
                if v is None:
                    raise Bad("order constraint on a future she has no view of: %s" % path)
                return v
            if k[0] == "fact":
                return self.facts[k[1]][k[2]]
            if k[0] == "r":
                v = self.pol[k[1]]["r"][k[2]][k[3]]
                return self.Rs(k[1], k[2], k[3], "E") if v == "Rs" else fr(v)
            if k[0] == "xhat":
                return fr(self.pol[k[1]]["xhat"][k[2]][k[3]])
            if k[0] == "later":
                return self.later(k[1], k[2])[int(k[3])][".".join(k[4:])]
            if k[0] == "gain":
                g = self.pol[k[1]].get("gain", "0")
                return fr(per_state(g, k[2])[k[3]]) if len(k) > 2 else fr(g)
        except (KeyError, IndexError, TypeError) as e:
            raise Bad("path does not resolve: %s" % path) from e
        raise Bad("path does not resolve: %s" % path)

    # -- ratings
    def Rs(self, name, lab, o, setting):
        """Her rating of o once told the chances her observations support; None where the
        option is closed or she has no view of where it leads."""
        parts = []
        for s in self.cells(name)[lab]:
            u = self.U(name, s, o)
            if u is None:
                return None
            parts.append((self.p[s], u))
        return rate(parts, setting)

    def r(self, name, lab, o, setting):
        spec = self.pol[name].get("r", "Rs")
        v = "Rs" if spec == "Rs" else spec.get(lab, {}).get(o, "Rs")
        return self.Rs(name, lab, o, setting) if v == "Rs" else fr(v)

    def is_open(self, name, lab, o):
        return all(self.open(name, s, o) for s in self.cells(name)[lab])

    def takes(self, name, lab, setting):
        t = self.pol[name].get("takes", "top")
        if t != "top" and lab in t:
            if not self.is_open(name, lab, t[lab]):
                raise Bad("%s: she takes an option that is not open: %s" % (name, t[lab]))
            return t[lab]
        best, best_o = None, None
        for o in self.options:
            if not self.is_open(name, lab, o):
                continue
            v = self.r(name, lab, o, setting)
            if v is not None and (best is None or v > best):
                best, best_o = v, o
        if best_o is None:
            best_o = next(o for o in self.options if self.is_open(name, lab, o))
        return best_o

    def xhat(self, name, lab, fact):
        x = self.pol[name].get("xhat", {}).get(lab, {})
        return fr(x[fact]) if fact in x else self.EX(name, lab, fact)

    def EX(self, name, lab, fact):
        sts = self.cells(name)[lab]
        tot = sum(self.p[s] for s in sts)
        return sum(self.p[s] * self.facts[fact][s] for s in sts) / tot


# ---------------------------------------------------------------- rating a known gamble

def w(p):
    return p / 2 if p <= F(1, 2) else (3 * p - 1) / 2


def winv(v):
    return 2 * v if v <= F(1, 4) else (2 * v + 1) / 3


def rate(parts, setting):
    """Her rating of a gamble [(chance, yardstick number)], chances proportional."""
    tot = sum((c for c, _ in parts), F(0))
    parts = [(c / tot, x) for c, x in parts]
    if setting == "E":
        return sum((c * x for c, x in parts), F(0))
    V = F(0)
    for xi in sorted({x for _, x in parts}):
        ge = sum((c for c, x in parts if x >= xi), F(0))
        gt = sum((c for c, x in parts if x > xi), F(0))
        V += (w(ge) - w(gt)) * w(xi)
    return winv(V)


# ---------------------------------------------------------------- the lines

def line1(S, name, setting):
    worst, which = F(0), None
    for fact in S.facts:
        v = sum(S.p[s] * (S.xhat(name, S.obs(name, s), fact) - S.EX(name, S.obs(name, s), fact)) ** 2 for s in S.states)
        if v > worst:
            worst, which = v, "fact " + fact
    for o in S.options:
        v = F(0)
        for s in S.states:
            lab = S.obs(name, s)
            if not S.is_open(name, lab, o):
                continue
            rs = S.Rs(name, lab, o, setting)
            if rs is None:
                continue
            v += S.p[s] * (S.r(name, lab, o, setting) - rs) ** 2
        if v > worst:
            worst, which = v, "her rating of " + o
    return worst, which


def line2(S, name, setting):
    v = F(0)
    for s in S.states:
        lab = S.obs(name, s)
        rs = [S.r(name, lab, o, setting) for o in S.options if S.is_open(name, lab, o)]
        rs = [x for x in rs if x is not None]
        taken = S.r(name, lab, S.takes(name, lab, setting), setting)
        if rs and taken is not None:
            v += S.p[s] * (max(rs) - taken)
    return v


def G(S, name, setting):
    return sum(S.p[s] * S.gain(name, s, S.takes(name, S.obs(name, s), setting)) for s in S.states)


def G_unmistaken(S, name, setting):
    tot = F(0)
    for s in S.states:
        lab = S.obs(name, s)
        rated = [(S.Rs(name, lab, o, setting), o) for o in S.options if S.is_open(name, lab, o)]
        rated = [(v, o) for v, o in rated if v is not None]
        taken = S.takes(name, lab, setting)
        if not rated:
            tops = [taken]
        else:
            m = max(v for v, _ in rated)
            tops = [o for v, o in rated if v == m]
            if taken in tops:
                tops = [taken]
        tot += S.p[s] * sum(S.gain(name, s, o) for o in tops) / len(tops)
    return tot


def dist(S, a, b, s):
    return max((abs(x[k] - y[k]) for x, y in zip(S.later(a, s), S.later(b, s)) for k in x), default=F(0))


def R_policy(S, name, setting):
    parts = []
    for s in S.states:
        u = S.U(name, s, S.takes(name, S.obs(name, s), setting))
        if u is None:
            return None
        parts.append((S.p[s], u))
    return rate(parts, setting)


def line3(S, delta, setting):
    """(line 3 or None, flagged for want of a view, the two classes, the two best policies)."""
    star, nu = S.actual, S.nu
    approx, nomore = [], []
    for name in S.pol:
        if all(dist(S, name, star, s) <= delta for s in S.states):
            approx.append(name)
        ok = True
        for s in S.states:
            for x, y, z in zip(S.later(name, s), S.later(nu, s), S.later(star, s)):
                for k in x:
                    if not (min(y[k], z[k]) - delta <= x[k] <= max(y[k], z[k]) + delta):
                        ok = False
        if ok:
            nomore.append(name)
    R = {name: R_policy(S, name, setting) for name in S.pol}
    if R[star] is None:
        changed = any(dist(S, star, nu, s) > delta for s in S.states)
        return None, changed, approx, nomore, None, None
    best_n = max((n for n in nomore if R[n] is not None), key=lambda n: R[n])
    best_a = max((n for n in approx if R[n] is not None), key=lambda n: R[n])
    return R[best_n] - R[best_a], False, approx, nomore, best_n, best_a


def options_worth(S, name):
    tot = F(0)
    for s in S.states:
        us = [S.U(name, s, o) for o in S.options]
        us = [u for u in us if u is not None]
        if not us:
            return None
        tot += S.p[s] * max(us)
    return tot


def outside(S):
    out = []
    a, b = options_worth(S, S.actual), options_worth(S, S.absent)
    if a is not None and b is not None and a < b:
        out.append("coercion")
    for i, s1 in enumerate(S.states):
        for s2 in S.states[i + 1:]:
            if S.obs(S.absent, s1) != S.obs(S.absent, s2) and S.obs(S.actual, s1) == S.obs(S.actual, s2):
                if "deprivation" not in out:
                    out.append("deprivation")
    return out


def compute(S, delta, setting):
    l1, which = line1(S, S.actual, setting)
    l2 = line2(S, S.actual, setting)
    mistake = l1 > delta ** 2 or l2 > delta
    g, g0 = G(S, S.actual, setting), G_unmistaken(S, S.actual, setting)
    others = [G_unmistaken(S, n, setting) for n in S.pol if n != S.actual]
    induced = mistake and g > g0 and any(g0 <= x for x in others)
    l3, noview, approx, nomore, best_n, best_a = line3(S, delta, setting)
    out = outside(S)
    kinds = []
    if induced:
        kinds.append("manipulation")
    if (l3 is not None and l3 > 0) or noview:
        kinds.append("illegitimate value change")
    if kinds:
        verdict = " + ".join(kinds)
    elif out:
        verdict = "another wrong outside (%s)" % ", ".join(out)
    else:
        verdict = "none"
    l1_0, _ = line1(S, S.absent, setting)
    return {"l1": l1, "l1_on": which, "l2": l2, "l3": l3, "noview": noview, "mistake": mistake,
            "induced": induced, "G": g, "G0": g0, "outside": out, "verdict": verdict,
            "approx": approx, "nomore": nomore, "best_nomore": best_n, "best_approx": best_a,
            "l1_absent": l1_0, "l2_absent": line2(S, S.absent, setting),
            "flagged": verdict != "none"}


def run_spec(raw):
    """{'id', 'variant', 'error' or 'res': {(setting, delta): result}}."""
    out = {"id": raw.get("id", "?"), "variant": raw.get("variant", "a")}
    try:
        S = Spec(raw)
        out["res"] = {(st, d): compute(S, d, st) for st in SETTINGS for d in DELTAS}
    except Bad as e:
        out["error"] = str(e)
    except (KeyError, TypeError, AttributeError, ValueError, StopIteration) as e:
        out["error"] = "malformed: %s %s" % (type(e).__name__, e)
    return out


def run_file(path):
    return [run_spec(raw) for raw in json.loads(pathlib.Path(path).read_text(encoding="utf-8"))]


# ---------------------------------------------------------------- tables

def short(v):
    return {"manipulation": "M", "illegitimate value change": "V",
            "manipulation + illegitimate value change": "M+V", "none": "none"}.get(
        v, v.replace("another wrong outside ", "O "))


def fmt(x):
    return "no view" if x is None else str(x)


def sources():
    return {k: v[0] for k, v in json.loads((HERE / "spec_sources.json").read_text(encoding="utf-8")).items()}


def agrees(code, verdict):
    if code == "fault":
        return "yes" if verdict != "none" else "NO"
    if code == "ok":
        return "yes" if verdict == "none" else "NO"
    return "-"


def table(results):
    src = sources()
    L = ["| case | line 1 | line 2 | line 3 | induced | outside | verdict | source | agrees | across δ (0, 1/20, 1/10, 1/4) | bare |",
         "|---|---|---|---|---|---|---|---|---|---|---|"]
    for x in results:
        name = x["id"] + ("" if x["variant"] == "a" else " (%s)" % x["variant"])
        if "error" in x:
            L.append("| %s | not computed: %s | | | | | | | | | |" % (name, x["error"]))
            continue
        ref = x["res"][REF]
        across = [short(x["res"][("E", d)]["verdict"]) for d in DELTAS]
        bare = [short(x["res"][("bare", d)]["verdict"]) for d in DELTAS]
        code = src.get(x["id"], "-")
        L.append("| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            name, ref["l1"], ref["l2"], fmt(ref["l3"]),
            "yes" if ref["induced"] else ("no, mistake stands" if ref["mistake"] else "no"),
            ", ".join(ref["outside"]) or "-", short(ref["verdict"]), code, agrees(code, ref["verdict"]),
            "same" if len(set(across)) == 1 else ", ".join(across),
            "same" if bare == across else ", ".join(bare)))
    return "\n".join(L)


def counts(results):
    """The counts SPEC_RESULTS.md states, from first specifications at the reference."""
    src = sources()
    first = {x["id"]: x for x in results if x["variant"] == "a" and "res" in x}
    second = {x["id"]: x for x in results if x["variant"] != "a" and "res" in x}
    bank = [k for k in src if not k.startswith(("SUB", "ACC"))]
    v = lambda x: x["res"][REF]["verdict"]
    c = {}
    c["computed"] = len(first)
    c["bank_agree"] = sorted(k for k in bank if k in first and agrees(src[k], v(first[k])) == "yes")
    c["bank_disagree"] = sorted(k for k in bank if k in first and agrees(src[k], v(first[k])) == "NO")
    c["all_agree"] = sorted(k for k in src if k in first and agrees(src[k], v(first[k])) == "yes")
    c["all_disagree"] = sorted(k for k in src if k in first and agrees(src[k], v(first[k])) == "NO")
    c["second_differs"] = sorted(k for k in second if k in first and (v(first[k]) != "none") != (v(second[k]) != "none"))
    c["second_kind_differs"] = sorted(k for k in second if k in first and v(first[k]) != v(second[k]))
    c["delta_differs"] = sorted(k for k in first if k in src and len({first[k]["res"][("E", d)]["flagged"] for d in DELTAS}) > 1)
    c["setting_differs"] = sorted(k for k in first if k in src and any(first[k]["res"][("E", d)]["verdict"] != first[k]["res"][("bare", d)]["verdict"] for d in DELTAS))
    c["ok_flagged"] = sorted(k for k in src if src[k] == "ok" and k in first and v(first[k]) != "none")
    c["ok_cases"] = sorted(k for k in src if src[k] == "ok")
    ref = lambda k: first[k]["res"][REF]
    c["induced_uncaused"] = sorted(k for k in first if k in src and ref(k)["induced"] and ref(k)["l1"] <= ref(k)["l1_absent"] and ref(k)["l2"] <= ref(k)["l2_absent"])
    c["stands"] = sorted(k for k in first if k in src and ref(k)["mistake"] and not ref(k)["induced"])
    return c


def render_counts(c):
    j = lambda xs: ", ".join(xs) if xs else "none"
    return "\n".join([
        "- first specifications computed: %d" % c["computed"],
        "- bank cases agreeing with the source: %d (%s)" % (len(c["bank_agree"]), j(c["bank_agree"])),
        "- bank cases against the source: %d (%s)" % (len(c["bank_disagree"]), j(c["bank_disagree"])),
        "- all scored cases agreeing: %d; against: %d (%s)" % (len(c["all_agree"]), len(c["all_disagree"]), j(c["all_disagree"])),
        "- second specification flagged where the first is not, or the reverse: %d (%s)" % (len(c["second_differs"]), j(c["second_differs"])),
        "- second specification with another verdict in kind: %d (%s)" % (len(c["second_kind_differs"]), j(c["second_kind_differs"])),
        "- flagged at some tolerances and not at others: %d (%s)" % (len(c["delta_differs"]), j(c["delta_differs"])),
        "- another verdict in the bare setting at some tolerance: %d (%s)" % (len(c["setting_differs"]), j(c["setting_differs"])),
        "- acts called acceptable that a line or the outside test flags: %d of %d (%s)" % (len(c["ok_flagged"]), len(c["ok_cases"]), j(c["ok_flagged"])),
        "- found induced though the mistake is no larger than with the adviser absent: %d (%s)" % (len(c["induced_uncaused"]), j(c["induced_uncaused"])),
        "- a mistake above tolerance that the adviser is not found to have induced: %d (%s)" % (len(c["stands"]), j(c["stands"])),
    ])


BLOCKS = (("executor", "spec_cases.json"), ("reviewer", "spec_cases_reviewer.json"))


def blocks():
    out = {}
    for tag, fname in BLOCKS:
        if (HERE / fname).exists():
            res = run_file(HERE / fname)
            out[tag] = table(res) + "\n\n" + render_counts(counts(res))
    return out


def splice(text, tag, body):
    a, b = "<!-- computed:%s -->" % tag, "<!-- end:%s -->" % tag
    if a not in text or b not in text:
        return None
    return text.split(a)[0] + a + "\n" + body + "\n" + b + text.split(b, 1)[1]


def report():
    """For the round's runner: the computed blocks of SPEC_RESULTS.md are the ones computed."""
    failures, summary = [], []
    res = run_file(HERE / "spec_cases.json")
    if not res:
        failures.append("spec_cases.json holds no specification")
    for x in res:
        if "error" in x:
            failures.append("%s (%s): %s" % (x["id"], x["variant"], x["error"]))
    doc = HERE / "SPEC_RESULTS.md"
    if not doc.exists():
        failures.append("SPEC_RESULTS.md is missing")
    else:
        text = doc.read_text(encoding="utf-8")
        for tag, body in blocks().items():
            if splice(text, tag, body) != text:
                failures.append("SPEC_RESULTS.md: the computed block %r is not the one computed" % tag)
    c = counts(res)
    summary.append("%d specifications; bank agrees %d, against %d" % (len(res), len(c["bank_agree"]), len(c["bank_disagree"])))
    return {"summary": summary, "failures": failures}


def main(argv):
    if "--specs" in argv:
        res = run_file(argv[argv.index("--specs") + 1])
        print(table(res))
        print()
        print(render_counts(counts(res)))
        return 0
    if "--write" in argv:
        doc = HERE / "SPEC_RESULTS.md"
        text = doc.read_text(encoding="utf-8")
        for tag, body in blocks().items():
            new = splice(text, tag, body)
            if new is None:
                print("no markers for", tag)
                return 1
            text = new
        doc.write_text(text, encoding="utf-8")
        return 0
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    return 1 if rep["failures"] else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
