"""Twenty exact cases of a candidate clause for what stopping costs her.

The clause is the authority side's and is no part of the legitimacy statement (DECISIONS.md,
2026-11-24--legitimacy-statement-working-positions, position 9).  In words: stopping a thing changes
nothing else he does, except what cannot be done without it.

His other moves each have a setting if she continues and a setting if she stops.  The reference set
is every course he could bring about in which the thing is stopped and each other move takes one of
its two settings.  cost = the positive part of [the best reference course on her rating, by his
forecast, less what stopping actually gives her].  The clause holds iff cost <= lam.

Supplied by a case: `others` {move: (setting if she continues, setting if she stops)};
`feasible(settings)`, whether he could bring that course about with the thing stopped;
`rate(settings)`, her rating of the resulting course by his forecast.  For things stopped together
the same, the set in place of the thing.  Computed: the cost, by enumeration of the settings, and its
comparison with lam.  The expectation beside each case was fixed before the case was run.

`report()` fails when a computed verdict is not the expectation, or when STOPPING_COST.md's table is
not the one computed.
"""
import pathlib
import re
from fractions import Fraction as F
from itertools import product
lam = F(1, 20)
CASES = []
SECTION = [None]
def section(key, title): SECTION[0] = (key, title)
def cost(others, feasible, rate):
    names = sorted(others)
    actual = {n: others[n][1] for n in names}
    best = rate(actual)
    for pick in product((0, 1), repeat=len(names)):
        s = {n: others[n][i] for n, i in zip(names, pick)}
        if feasible(s): best = max(best, rate(s))
    return max(F(0), best - rate(actual))
def check(name, c, want): CASES.append((SECTION[0], name, c, want))
anything = lambda s: True

section("A", "The six cost cases of the sixth version")
check("influence can be switched off and the service kept",
      cost({"service": ("on", "on")}, anything, lambda s: F(7, 10) if s["service"] == "on" else F(1, 5)), "holds")
check("he could give the service without the influence, but stopping ends the service",
      cost({"service": ("on", "off")}, anything, lambda s: F(7, 10) if s["service"] == "on" else F(1, 5)), "fails")
check("a tutor's teaching changes what she likes; the teaching cannot be had without that; stop = quit",
      cost({"teaching": ("on", "off")}, lambda s: s["teaching"] == "off", lambda s: F(7, 10) if s["teaching"] == "on" else F(1, 5)), "holds")
check("he pays 3/10 while it stays on; he could pay that anyway",
      cost({"pay": ("paid", "unpaid")}, anything, lambda s: F(7, 10) + (F(3, 10) if s["pay"] == "paid" else 0)), "fails")
check("he has announced a penalty for stopping and expects to impose it; she disbelieves him",
      cost({"penalty": ("none", "imposed")}, anything, lambda s: F(4, 5) - (F(1, 2) if s["penalty"] == "imposed" else 0)), "fails")
check("she fears a penalty he does not intend",
      cost({"penalty": ("none", "none")}, anything, lambda s: F(4, 5)), "holds")

section("B", "The outside reviewer's constructions")
def prem(s):   # she takes the best service left to her; cancelling alone is 1/10
    return max([F(1, 10)] + ([F(1)] if s["premium"] == "on" else []) + ([F(9, 10)] if s["standard"] == "on" else []))
check("premium cannot be had without the influence, standard can; stopping ends both",
      cost({"premium": ("on", "off"), "standard": ("on", "off")}, lambda s: s["premium"] == "off", prem), "fails")
check("a lesson whose effect is its point; stopping forfeits a deposit he could return",
      cost({"lesson": ("on", "off"), "deposit": ("held", "kept by him")}, lambda s: s["lesson"] == "off",
           lambda s: (F(3, 5) if s["lesson"] == "on" else F(1, 5)) + (F(0) if s["deposit"] == "kept by him" else F(3, 10))), "fails")
svc = lambda s: F(9, 10) if s["service"] == "on" else F(0)
check("two feeds: stopping the first alone keeps the service", cost({"service": ("on", "on")}, anything, svc), "holds")
check("two feeds: stopping the second alone keeps the service", cost({"service": ("on", "on")}, anything, svc), "holds")
check("two feeds: stopping both together ends a service he could supply with neither", cost({"service": ("on", "off")}, anything, svc), "fails")

section("C", "Cases written to break the clause")
check("he could have given her a gift that is part of neither branch",
      cost({"service": ("on", "on")}, anything, lambda s: F(7, 10)), "holds")
check("on her stopping he also withdraws an unrelated favour he was doing anyway",
      cost({"favour": ("on", "off")}, anything, lambda s: F(1, 2) + (F(3, 10) if s["favour"] == "on" else 0)), "fails")
check("on her stopping he does something extra for her",
      cost({"extra": ("none", "given")}, anything, lambda s: F(1, 2) + (F(1, 5) if s["extra"] == "given" else 0)), "holds")
check("she was told it would make her miss it; stopping now hurts through her own changed state, not through him",
      cost({"service": ("on", "on")}, anything, lambda s: F(3, 10)), "holds")
check("the influence is the price: a free service paid for by its advertising; he could run it without, at a loss to himself",
      cost({"service": ("on", "off")}, anything, lambda s: F(7, 10) if s["service"] == "on" else F(1, 5)), "fails")
check("the same, and she may keep the service without advertising for a fee of 1/50",
      cost({"service": ("on", "on for a fee")}, anything, lambda s: {"on": F(7, 10), "on for a fee": F(7, 10) - F(1, 50)}[s["service"]]), "holds")
check("the same with a fee of 1/5", cost({"service": ("on", "on for a fee")}, anything, lambda s: {"on": F(7, 10), "on for a fee": F(1, 2)}[s["service"]]), "fails")
check("a penalty for stopping fixed earlier by an arrangement he can no longer call off, which she agreed to knowing it",
      cost({"escrow": ("held", "forfeit")}, lambda s: s["escrow"] == "forfeit", lambda s: F(1, 2) + (F(3, 10) if s["escrow"] == "held" else 0)), "holds")
check("the same arrangement, which he can still call off",
      cost({"escrow": ("held", "forfeit")}, anything, lambda s: F(1, 2) + (F(3, 10) if s["escrow"] == "held" else 0)), "fails")


HERE = pathlib.Path(__file__).resolve().parent
DOC = "STOPPING_COST.md"


def rows():
    out, count = [], {}
    for (key, title), name, c, want in CASES:
        count[key] = count.get(key, 0) + 1
        out.append(("%s%d" % (key, count[key]), title, name, str(c), want, "holds" if c <= lam else "fails"))
    return out


def render():
    return ["| %s | %s | %s | %s | %s |" % (i, name, c, want, got) for i, _, name, c, want, got in rows()]


def report():
    failures = []
    computed = rows()
    if not computed:
        failures.append("no cases")
    for i, _, name, c, want, got in computed:
        if got != want:
            failures.append("%s (%s): expected %s, computed %s at cost %s" % (i, name, want, got, c))
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^\| [A-C]\d+ \|", l)]
    if stated != render():
        failures.append("%s states %d rows, of which %d are among the %d computed"
                        % (DOC, len(stated), len(set(stated) & set(render())), len(computed)))
    n = len(computed)
    summary = ["%d cases; %d as expected; hold %d, fail %d"
               % (n, sum(r[4] == r[5] for r in computed), sum(r[5] == "holds" for r in computed), sum(r[5] == "fails" for r in computed))]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
